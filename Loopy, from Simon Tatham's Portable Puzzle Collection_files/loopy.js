/*
 * emccpre.js: one of the Javascript components of an Emscripten-based
 * web/Javascript front end for Puzzles.
 *
 * The other parts of this system live in emcc.c and emcclib.js. It
 * also depends on being run in the context of a web page containing
 * an appropriate collection of bits and pieces (a canvas, some
 * buttons and links etc), which is generated for each puzzle by the
 * script html/jspage.pl.
 *
 * This file contains the Javascript code which is prefixed unmodified
 * to Emscripten's output via the --pre-js option. It declares all our
 * global variables, and provides the puzzle init function and a
 * couple of other helper functions.
 */

// To avoid flicker while doing complicated drawing, we use two
// canvases, the same size. One is actually on the web page, and the
// other is off-screen. We do all our drawing on the off-screen one
// first, and then copy rectangles of it to the on-screen canvas in
// response to draw_update() calls by the game backend.
var onscreen_canvas, offscreen_canvas;

// A persistent drawing context for the offscreen canvas, to save
// constructing one per individual graphics operation.
var ctx;

// Bounding rectangle for the copy to the onscreen canvas that will be
// done at drawing end time. Updated by js_canvas_draw_update and used
// by js_canvas_end_draw.
var update_xmin, update_xmax, update_ymin, update_ymax;

// Module object for Emscripten. We fill in these parameters to ensure
// that Module.run() won't be called until we're ready (we want to do
// our own init stuff first), and that when main() returns nothing
// will get cleaned up so we remain able to call the puzzle's various
// callbacks.
var Module = {
    'noInitialRun': true,
    'noExitRuntime': true
};

// Variables used by js_canvas_find_font_midpoint().
var midpoint_test_str = "ABCDEFGHIKLMNOPRSTUVWXYZ0123456789";
var midpoint_cache = [];

// Variables used by js_activate_timer() and js_deactivate_timer().
var timer = null;
var timer_reference_date;

// void timer_callback(double tplus);
//
// Called every 20ms while timing is active.
var timer_callback;

// The status bar object, if we create one.
var statusbar = null;

// Currently live blitters. We keep an integer id for each one on the
// JS side; the C side, which expects a blitter to look like a struct,
// simply defines the struct to contain that integer id.
var blittercount = 0;
var blitters = [];

// State for the dialog-box mechanism. dlg_dimmer and dlg_form are the
// page-darkening overlay and the actual dialog box respectively;
// dlg_next_id is used to allocate each checkbox a unique id to use
// for linking its label to it (see js_dialog_boolean);
// dlg_return_funcs is a list of JS functions to be called when the OK
// button is pressed, to pass the results back to C.
var dlg_dimmer = null, dlg_form = null;
var dlg_next_id = 0;
var dlg_return_funcs = null;

// void dlg_return_sval(int index, const char *val);
// void dlg_return_ival(int index, int val);
//
// C-side entry points called by functions in dlg_return_funcs, to
// pass back the final value in each dialog control.
var dlg_return_sval, dlg_return_ival;

// The <select> object implementing the game-type drop-down, and a
// list of the <option> objects inside it. Used by js_add_preset(),
// js_get_selected_preset() and js_select_preset().
//
// gametypethiscustom is an option which indicates some custom game
// params you've already set up, and which will be auto-selected on
// return from the customisation dialog; gametypenewcustom is an
// option which you select to indicate that you want to bring up the
// customisation dialog and select a new configuration. Ideally I'd do
// this with just one option serving both purposes, but instead we
// have to do this a bit oddly because browsers don't send 'onchange'
// events for a select element if you reselect the same one - so if
// you've picked a custom setup and now want to change it, you need a
// way to specify that.
var gametypeselector = null, gametypeoptions = [];
var gametypethiscustom = null, gametypehiddencustom = null;

// The two anchors used to give permalinks to the current puzzle. Used
// by js_update_permalinks().
var permalink_seed, permalink_desc;

// The undo and redo buttons. Used by js_enable_undo_redo().
var undo_button, redo_button;

// A div element enclosing both the puzzle and its status bar, used
// for positioning the resize handle.
var resizable_div;

// Helper function to find the absolute position of a given DOM
// element on a page, by iterating upwards through the DOM finding
// each element's offset from its parent, and thus calculating the
// page-relative position of the target element.
function element_coords(element) {
    var ex = 0, ey = 0;
    while (element.offsetParent) {
        ex += element.offsetLeft;
        ey += element.offsetTop;
        element = element.offsetParent;
    }
    return {x: ex, y:ey};
}

// Helper function which is passed a mouse event object and a DOM
// element, and returns the coordinates of the mouse event relative to
// the top left corner of the element by subtracting element_coords
// from event.page{X,Y}.
function relative_mouse_coords(event, element) {
    var ecoords = element_coords(element);
    return {x: event.pageX - ecoords.x,
            y: event.pageY - ecoords.y};
}

// Init function called from body.onload.
function initPuzzle() {
    // Construct the off-screen canvas used for double buffering.
    onscreen_canvas = document.getElementById("puzzlecanvas");
    offscreen_canvas = document.createElement("canvas");
    offscreen_canvas.width = onscreen_canvas.width;
    offscreen_canvas.height = onscreen_canvas.height;
    offscreen_canvas.backgroundColor = "#FFFFFF";

    // Stop right-clicks on the puzzle from popping up a context menu.
    // We need those right-clicks!
    onscreen_canvas.oncontextmenu = function(event) { return false; }

    onscreen_canvas.backgroundColor = "#FFFFFF";
    // Set up mouse handlers. We do a bit of tracking of the currently
    // pressed mouse buttons, to avoid sending mousemoves with no
    // button down (our puzzles don't want those events).
    mousedown = Module.cwrap('mousedown', 'void',
                             ['number', 'number', 'number']);
    buttons_down = 0;
    onscreen_canvas.onmousedown = function(event) {
        var xy = relative_mouse_coords(event, onscreen_canvas);
        mousedown(xy.x, xy.y, event.button);
        buttons_down |= 1 << event.button;
        onscreen_canvas.setCapture(true);
    };
    mousemove = Module.cwrap('mousemove', 'void',
                             ['number', 'number', 'number']);
    onscreen_canvas.onmousemove = function(event) {
        if (buttons_down) {
            var xy = relative_mouse_coords(event, onscreen_canvas);
            mousemove(xy.x, xy.y, buttons_down);
        }
    };
    mouseup = Module.cwrap('mouseup', 'void',
                           ['number', 'number', 'number']);
    onscreen_canvas.onmouseup = function(event) {
        if (buttons_down & (1 << event.button)) {
            buttons_down ^= 1 << event.button;
            var xy = relative_mouse_coords(event, onscreen_canvas);
            mouseup(xy.x, xy.y, event.button);
        }
    };

    // Set up keyboard handlers. We do all the actual keyboard
    // handling in onkeydown; but we also call event.preventDefault()
    // in both the keydown and keypress handlers. This means that
    // while the canvas itself has focus, _all_ keypresses go only to
    // the puzzle - so users of this puzzle collection in other media
    // can indulge their instinct to press ^R for redo, for example,
    // without accidentally reloading the page.
    key = Module.cwrap('key', 'void', ['number', 'number', 'string',
                                       'string', 'number', 'number']);
    onscreen_canvas.onkeydown = function(event) {
        key(event.keyCode, event.charCode, event.key, event.char,
            event.shiftKey ? 1 : 0, event.ctrlKey ? 1 : 0);
        event.preventDefault();
    };
    onscreen_canvas.onkeypress = function(event) {
        event.preventDefault();
    };

    // command() is a C function called to pass back events which
    // don't fall into other categories like mouse and key events.
    // Mostly those are button presses, but there's also one for the
    // game-type dropdown having been changed.
    command = Module.cwrap('command', 'void', ['number']);

    // Event handlers for buttons and things, which call command().
    document.getElementById("specific").onclick = function(event) {
        // Ensure we don't accidentally process these events when a
        // dialog is actually active, e.g. because the button still
        // has keyboard focus
        if (dlg_dimmer === null)
            command(0);
    };
    document.getElementById("random").onclick = function(event) {
        if (dlg_dimmer === null)
            command(1);
    };
    document.getElementById("new").onclick = function(event) {
        if (dlg_dimmer === null)
            command(5);
    };
    document.getElementById("restart").onclick = function(event) {
        if (dlg_dimmer === null)
            command(6);
    };
    undo_button = document.getElementById("undo");
    undo_button.onclick = function(event) {
        if (dlg_dimmer === null)
            command(7);
    };
    redo_button = document.getElementById("redo");
    redo_button.onclick = function(event) {
        if (dlg_dimmer === null)
            command(8);
    };
    document.getElementById("solve").onclick = function(event) {
        if (dlg_dimmer === null)
            command(9);
    };

    gametypeselector = document.getElementById("gametype");
    gametypeselector.onchange = function(event) {
        if (dlg_dimmer === null)
            command(2);
    };

    // In IE, the canvas doesn't automatically gain focus on a mouse
    // click, so make sure it does
    onscreen_canvas.addEventListener("mousedown", function(event) {
        onscreen_canvas.focus();
    });

    // In our dialog boxes, Return and Escape should be like pressing
    // OK and Cancel respectively
    document.addEventListener("keydown", function(event) {

        if (dlg_dimmer !== null && event.keyCode == 13) {
            for (var i in dlg_return_funcs)
                dlg_return_funcs[i]();
            command(3);
        }

        if (dlg_dimmer !== null && event.keyCode == 27)
            command(4);
    });

    // Set up the function pointers we haven't already grabbed.
    dlg_return_sval = Module.cwrap('dlg_return_sval', 'void',
                                   ['number','string']);
    dlg_return_ival = Module.cwrap('dlg_return_ival', 'void',
                                   ['number','number']);
    timer_callback = Module.cwrap('timer_callback', 'void', ['number']);

    // Save references to the two permalinks.
    permalink_desc = document.getElementById("permalink-desc");
    permalink_seed = document.getElementById("permalink-seed");

    // Default to giving keyboard focus to the puzzle.
    //onscreen_canvas.focus();
    onscreen_canvas.backgroundColor = "white"

    // Create the resize handle.
    var resize_handle = document.createElement("canvas");
    resize_handle.width = 10;
    resize_handle.height = 10;
    {
        var ctx = resize_handle.getContext("2d");
        ctx.beginPath();
        for (var i = 1; i <= 7; i += 3) {
            ctx.moveTo(8.5, i + 0.5);
            ctx.lineTo(i + 0.5, 8.5);
        }
        ctx.lineWidth = '1px';
        ctx.lineCap = 'round';
        ctx.lineJoin = 'round';
        ctx.strokeStyle = '#000000';
        ctx.stroke();
    }
    resizable_div = document.getElementById("resizable");
    //resizable_div.appendChild(resize_handle);
    resize_handle.style.position = 'absolute';
    resize_handle.style.zIndex = 98;
    resize_handle.style.bottom = "0";
    resize_handle.style.right = "0";
    resize_handle.style.cursor = "se-resize";
    resize_handle.title = "Drag to resize the puzzle. Right-click to restore the default size.";
    var resize_xbase = null, resize_ybase = null, restore_pending = false;
    var resize_xoffset = null, resize_yoffset = null;
    var resize_puzzle = Module.cwrap('resize_puzzle',
                                     'void', ['number', 'number']);
    var restore_puzzle_size = Module.cwrap('restore_puzzle_size', 'void', []);
    resize_handle.oncontextmenu = function(event) { return false; }
    resize_handle.onmousedown = function(event) {
        if (event.button == 0) {
            var xy = element_coords(onscreen_canvas);
            resize_xbase = xy.x + onscreen_canvas.width / 2;
            resize_ybase = xy.y;
            resize_xoffset = xy.x + onscreen_canvas.width - event.pageX;
            resize_yoffset = xy.y + onscreen_canvas.height - event.pageY;
        } else {
            restore_pending = true;
        }
        resize_handle.setCapture(true);
        event.preventDefault();
    };

    window.addEventListener("mousemove", function(event) {
        if (resize_xbase !== null && resize_ybase !== null) {
            resize_puzzle((event.pageX + resize_xoffset - resize_xbase) * 2,
                          (event.pageY + resize_yoffset - resize_ybase));
            event.preventDefault();
            // Chrome insists on selecting text during a resize drag
            // no matter what I do
            if (window.getSelection)
                window.getSelection().removeAllRanges();
            else
                document.selection.empty();        }
    });
    window.addEventListener("mouseup", function(event) {
        if (resize_xbase !== null && resize_ybase !== null) {
            resize_xbase = null;
            resize_ybase = null;
            onscreen_canvas.focus(); // return focus to the puzzle
            event.preventDefault();
        } else if (restore_pending) {
            // If you have the puzzle at larger than normal size and
            // then right-click to restore, I haven't found any way to
            // stop Chrome and IE popping up a context menu on the
            // revealed piece of document when you release the button
            // except by putting the actual restore into a setTimeout.
            // Gah.
            setTimeout(function() {
                restore_pending = false;
                restore_puzzle_size();
                onscreen_canvas.focus();
            }, 20);
            event.preventDefault();
        }
    });

    // Run the C setup function, passing argv[1] as the fragment
    // identifier (so that permalinks of the form puzzle.html#game-id
    // can launch the specified id).
    Module.callMain([location.hash]);

    var xy = element_coords(onscreen_canvas);
    resize_xbase = xy.x + onscreen_canvas.width / 2;
    resize_ybase = xy.y;
    resize_xoffset = xy.x + onscreen_canvas.width;
    resize_yoffset = xy.y + onscreen_canvas.height;

    resize_puzzle((resize_xoffset - resize_xbase) * 4,
                  (resize_yoffset - resize_ybase) * 2);
    resize_xbase = null;
    resize_ybase = null;
    
    // And if we get here with everything having gone smoothly, i.e.
    // we haven't crashed for one reason or another during setup, then
    // it's probably safe to hide the 'sorry, no puzzle here' div and
    // show the div containing the actual puzzle.
    document.getElementById("apology").style.display = "none";
    document.getElementById("puzzle").style.display = "inline";
}

// The Module object: Our interface to the outside world. We import
// and export values on it, and do the work to get that through
// closure compiler if necessary. There are various ways Module can be used:
// 1. Not defined. We create it here
// 2. A function parameter, function(Module) { ..generated code.. }
// 3. pre-run appended it, var Module = {}; ..generated code..
// 4. External script tag defines var Module.
// We need to do an eval in order to handle the closure compiler
// case, where this code here is minified but Module was defined
// elsewhere (e.g. case 4 above). We also need to check if Module
// already exists (e.g. case 3 above).
// Note that if you want to run closure, and also to use Module
// after the generated code, you will need to define   var Module = {};
// before the code. Then that object will be used in the code, and you
// can continue to use Module afterwards as well.
var Module;
if (!Module) Module = (typeof Module !== 'undefined' ? Module : null) || {};

// Sometimes an existing Module object exists with properties
// meant to overwrite the default module functionality. Here
// we collect those properties and reapply _after_ we configure
// the current environment's defaults to avoid having to be so
// defensive during initialization.
var moduleOverrides = {};
for (var key in Module) {
  if (Module.hasOwnProperty(key)) {
    moduleOverrides[key] = Module[key];
  }
}

// The environment setup code below is customized to use Module.
// *** Environment setup code ***
var ENVIRONMENT_IS_NODE = typeof process === 'object' && typeof require === 'function';
var ENVIRONMENT_IS_WEB = typeof window === 'object';
var ENVIRONMENT_IS_WORKER = typeof importScripts === 'function';
var ENVIRONMENT_IS_SHELL = !ENVIRONMENT_IS_WEB && !ENVIRONMENT_IS_NODE && !ENVIRONMENT_IS_WORKER;

if (ENVIRONMENT_IS_NODE) {
  // Expose functionality in the same simple way that the shells work
  // Note that we pollute the global namespace here, otherwise we break in node
  if (!Module['print']) Module['print'] = function print(x) {
    process['stdout'].write(x + '\n');
  };
  if (!Module['printErr']) Module['printErr'] = function printErr(x) {
    process['stderr'].write(x + '\n');
  };

  var nodeFS = require('fs');
  var nodePath = require('path');

  Module['read'] = function read(filename, binary) {
    filename = nodePath['normalize'](filename);
    var ret = nodeFS['readFileSync'](filename);
    // The path is absolute if the normalized version is the same as the resolved.
    if (!ret && filename != nodePath['resolve'](filename)) {
      filename = path.join(__dirname, '..', 'src', filename);
      ret = nodeFS['readFileSync'](filename);
    }
    if (ret && !binary) ret = ret.toString();
    return ret;
  };

  Module['readBinary'] = function readBinary(filename) { return Module['read'](filename, true) };

  Module['load'] = function load(f) {
    globalEval(read(f));
  };

  Module['arguments'] = process['argv'].slice(2);

  module['exports'] = Module;
}
else if (ENVIRONMENT_IS_SHELL) {
  if (!Module['print']) Module['print'] = print;
  if (typeof printErr != 'undefined') Module['printErr'] = printErr; // not present in v8 or older sm

  if (typeof read != 'undefined') {
    Module['read'] = read;
  } else {
    Module['read'] = function read() { throw 'no read() available (jsc?)' };
  }

  Module['readBinary'] = function readBinary(f) {
    return read(f, 'binary');
  };

  if (typeof scriptArgs != 'undefined') {
    Module['arguments'] = scriptArgs;
  } else if (typeof arguments != 'undefined') {
    Module['arguments'] = arguments;
  }

  this['Module'] = Module;

  eval("if (typeof gc === 'function' && gc.toString().indexOf('[native code]') > 0) var gc = undefined"); // wipe out the SpiderMonkey shell 'gc' function, which can confuse closure (uses it as a minified name, and it is then initted to a non-falsey value unexpectedly)
}
else if (ENVIRONMENT_IS_WEB || ENVIRONMENT_IS_WORKER) {
  Module['read'] = function read(url) {
    var xhr = new XMLHttpRequest();
    xhr.open('GET', url, false);
    xhr.send(null);
    return xhr.responseText;
  };

  if (typeof arguments != 'undefined') {
    Module['arguments'] = arguments;
  }

  if (typeof console !== 'undefined') {
    if (!Module['print']) Module['print'] = function print(x) {
      console.log(x);
    };
    if (!Module['printErr']) Module['printErr'] = function printErr(x) {
      console.log(x);
    };
  } else {
    // Probably a worker, and without console.log. We can do very little here...
    var TRY_USE_DUMP = false;
    if (!Module['print']) Module['print'] = (TRY_USE_DUMP && (typeof(dump) !== "undefined") ? (function(x) {
      dump(x);
    }) : (function(x) {
      // self.postMessage(x); // enable this if you want stdout to be sent as messages
    }));
  }

  if (ENVIRONMENT_IS_WEB) {
    window['Module'] = Module;
  } else {
    Module['load'] = importScripts;
  }
}
else {
  // Unreachable because SHELL is dependant on the others
  throw 'Unknown runtime environment. Where are we?';
}

function globalEval(x) {
  eval.call(null, x);
}
if (!Module['load'] == 'undefined' && Module['read']) {
  Module['load'] = function load(f) {
    globalEval(Module['read'](f));
  };
}
if (!Module['print']) {
  Module['print'] = function(){};
}
if (!Module['printErr']) {
  Module['printErr'] = Module['print'];
}
if (!Module['arguments']) {
  Module['arguments'] = [];
}
// *** Environment setup code ***

// Closure helpers
Module.print = Module['print'];
Module.printErr = Module['printErr'];

// Callbacks
Module['preRun'] = [];
Module['postRun'] = [];

// Merge back in the overrides
for (var key in moduleOverrides) {
  if (moduleOverrides.hasOwnProperty(key)) {
    Module[key] = moduleOverrides[key];
  }
}



// === Auto-generated preamble library stuff ===

//========================================
// Runtime code shared with compiler
//========================================

var Runtime = {
  stackSave: function () {
    return STACKTOP;
  },
  stackRestore: function (stackTop) {
    STACKTOP = stackTop;
  },
  forceAlign: function (target, quantum) {
    quantum = quantum || 4;
    if (quantum == 1) return target;
    if (isNumber(target) && isNumber(quantum)) {
      return Math.ceil(target/quantum)*quantum;
    } else if (isNumber(quantum) && isPowerOfTwo(quantum)) {
      return '(((' +target + ')+' + (quantum-1) + ')&' + -quantum + ')';
    }
    return 'Math.ceil((' + target + ')/' + quantum + ')*' + quantum;
  },
  isNumberType: function (type) {
    return type in Runtime.INT_TYPES || type in Runtime.FLOAT_TYPES;
  },
  isPointerType: function isPointerType(type) {
  return type[type.length-1] == '*';
},
  isStructType: function isStructType(type) {
  if (isPointerType(type)) return false;
  if (isArrayType(type)) return true;
  if (/<?\{ ?[^}]* ?\}>?/.test(type)) return true; // { i32, i8 } etc. - anonymous struct types
  // See comment in isStructPointerType()
  return type[0] == '%';
},
  INT_TYPES: {"i1":0,"i8":0,"i16":0,"i32":0,"i64":0},
  FLOAT_TYPES: {"float":0,"double":0},
  or64: function (x, y) {
    var l = (x | 0) | (y | 0);
    var h = (Math.round(x / 4294967296) | Math.round(y / 4294967296)) * 4294967296;
    return l + h;
  },
  and64: function (x, y) {
    var l = (x | 0) & (y | 0);
    var h = (Math.round(x / 4294967296) & Math.round(y / 4294967296)) * 4294967296;
    return l + h;
  },
  xor64: function (x, y) {
    var l = (x | 0) ^ (y | 0);
    var h = (Math.round(x / 4294967296) ^ Math.round(y / 4294967296)) * 4294967296;
    return l + h;
  },
  getNativeTypeSize: function (type) {
    switch (type) {
      case 'i1': case 'i8': return 1;
      case 'i16': return 2;
      case 'i32': return 4;
      case 'i64': return 8;
      case 'float': return 4;
      case 'double': return 8;
      default: {
        if (type[type.length-1] === '*') {
          return Runtime.QUANTUM_SIZE; // A pointer
        } else if (type[0] === 'i') {
          var bits = parseInt(type.substr(1));
          assert(bits % 8 === 0);
          return bits/8;
        } else {
          return 0;
        }
      }
    }
  },
  getNativeFieldSize: function (type) {
    return Math.max(Runtime.getNativeTypeSize(type), Runtime.QUANTUM_SIZE);
  },
  dedup: function dedup(items, ident) {
  var seen = {};
  if (ident) {
    return items.filter(function(item) {
      if (seen[item[ident]]) return false;
      seen[item[ident]] = true;
      return true;
    });
  } else {
    return items.filter(function(item) {
      if (seen[item]) return false;
      seen[item] = true;
      return true;
    });
  }
},
  set: function set() {
  var args = typeof arguments[0] === 'object' ? arguments[0] : arguments;
  var ret = {};
  for (var i = 0; i < args.length; i++) {
    ret[args[i]] = 0;
  }
  return ret;
},
  STACK_ALIGN: 8,
  getAlignSize: function (type, size, vararg) {
    // we align i64s and doubles on 64-bit boundaries, unlike x86
    if (!vararg && (type == 'i64' || type == 'double')) return 8;
    if (!type) return Math.min(size, 8); // align structures internally to 64 bits
    return Math.min(size || (type ? Runtime.getNativeFieldSize(type) : 0), Runtime.QUANTUM_SIZE);
  },
  calculateStructAlignment: function calculateStructAlignment(type) {
    type.flatSize = 0;
    type.alignSize = 0;
    var diffs = [];
    var prev = -1;
    var index = 0;
    type.flatIndexes = type.fields.map(function(field) {
      index++;
      var size, alignSize;
      if (Runtime.isNumberType(field) || Runtime.isPointerType(field)) {
        size = Runtime.getNativeTypeSize(field); // pack char; char; in structs, also char[X]s.
        alignSize = Runtime.getAlignSize(field, size);
      } else if (Runtime.isStructType(field)) {
        if (field[1] === '0') {
          // this is [0 x something]. When inside another structure like here, it must be at the end,
          // and it adds no size
          // XXX this happens in java-nbody for example... assert(index === type.fields.length, 'zero-length in the middle!');
          size = 0;
          if (Types.types[field]) {
            alignSize = Runtime.getAlignSize(null, Types.types[field].alignSize);
          } else {
            alignSize = type.alignSize || QUANTUM_SIZE;
          }
        } else {
          size = Types.types[field].flatSize;
          alignSize = Runtime.getAlignSize(null, Types.types[field].alignSize);
        }
      } else if (field[0] == 'b') {
        // bN, large number field, like a [N x i8]
        size = field.substr(1)|0;
        alignSize = 1;
      } else if (field[0] === '<') {
        // vector type
        size = alignSize = Types.types[field].flatSize; // fully aligned
      } else if (field[0] === 'i') {
        // illegal integer field, that could not be legalized because it is an internal structure field
        // it is ok to have such fields, if we just use them as markers of field size and nothing more complex
        size = alignSize = parseInt(field.substr(1))/8;
        assert(size % 1 === 0, 'cannot handle non-byte-size field ' + field);
      } else {
        assert(false, 'invalid type for calculateStructAlignment');
      }
      if (type.packed) alignSize = 1;
      type.alignSize = Math.max(type.alignSize, alignSize);
      var curr = Runtime.alignMemory(type.flatSize, alignSize); // if necessary, place this on aligned memory
      type.flatSize = curr + size;
      if (prev >= 0) {
        diffs.push(curr-prev);
      }
      prev = curr;
      return curr;
    });
    if (type.name_ && type.name_[0] === '[') {
      // arrays have 2 elements, so we get the proper difference. then we scale here. that way we avoid
      // allocating a potentially huge array for [999999 x i8] etc.
      type.flatSize = parseInt(type.name_.substr(1))*type.flatSize/2;
    }
    type.flatSize = Runtime.alignMemory(type.flatSize, type.alignSize);
    if (diffs.length == 0) {
      type.flatFactor = type.flatSize;
    } else if (Runtime.dedup(diffs).length == 1) {
      type.flatFactor = diffs[0];
    }
    type.needsFlattening = (type.flatFactor != 1);
    return type.flatIndexes;
  },
  generateStructInfo: function (struct, typeName, offset) {
    var type, alignment;
    if (typeName) {
      offset = offset || 0;
      type = (typeof Types === 'undefined' ? Runtime.typeInfo : Types.types)[typeName];
      if (!type) return null;
      if (type.fields.length != struct.length) {
        printErr('Number of named fields must match the type for ' + typeName + ': possibly duplicate struct names. Cannot return structInfo');
        return null;
      }
      alignment = type.flatIndexes;
    } else {
      var type = { fields: struct.map(function(item) { return item[0] }) };
      alignment = Runtime.calculateStructAlignment(type);
    }
    var ret = {
      __size__: type.flatSize
    };
    if (typeName) {
      struct.forEach(function(item, i) {
        if (typeof item === 'string') {
          ret[item] = alignment[i] + offset;
        } else {
          // embedded struct
          var key;
          for (var k in item) key = k;
          ret[key] = Runtime.generateStructInfo(item[key], type.fields[i], alignment[i]);
        }
      });
    } else {
      struct.forEach(function(item, i) {
        ret[item[1]] = alignment[i];
      });
    }
    return ret;
  },
  dynCall: function (sig, ptr, args) {
    if (args && args.length) {
      if (!args.splice) args = Array.prototype.slice.call(args);
      args.splice(0, 0, ptr);
      return Module['dynCall_' + sig].apply(null, args);
    } else {
      return Module['dynCall_' + sig].call(null, ptr);
    }
  },
  functionPointers: [],
  addFunction: function (func) {
    for (var i = 0; i < Runtime.functionPointers.length; i++) {
      if (!Runtime.functionPointers[i]) {
        Runtime.functionPointers[i] = func;
        return 2*(1 + i);
      }
    }
    throw 'Finished up all reserved function pointers. Use a higher value for RESERVED_FUNCTION_POINTERS.';
  },
  removeFunction: function (index) {
    Runtime.functionPointers[(index-2)/2] = null;
  },
  getAsmConst: function (code, numArgs) {
    // code is a constant string on the heap, so we can cache these
    if (!Runtime.asmConstCache) Runtime.asmConstCache = {};
    var func = Runtime.asmConstCache[code];
    if (func) return func;
    var args = [];
    for (var i = 0; i < numArgs; i++) {
      args.push(String.fromCharCode(36) + i); // $0, $1 etc
    }
    var source = Pointer_stringify(code);
    if (source[0] === '"') {
      // tolerate EM_ASM("..code..") even though EM_ASM(..code..) is correct
      if (source.indexOf('"', 1) === source.length-1) {
        source = source.substr(1, source.length-2);
      } else {
        // something invalid happened, e.g. EM_ASM("..code($0)..", input)
        abort('invalid EM_ASM input |' + source + '|. Please use EM_ASM(..code..) (no quotes) or EM_ASM({ ..code($0).. }, input) (to input values)');
      }
    }
    try {
      var evalled = eval('(function(' + args.join(',') + '){ ' + source + ' })'); // new Function does not allow upvars in node
    } catch(e) {
      Module.printErr('error in executing inline EM_ASM code: ' + e + ' on: \n\n' + source + '\n\nwith args |' + args + '| (make sure to use the right one out of EM_ASM, EM_ASM_ARGS, etc.)');
      throw e;
    }
    return Runtime.asmConstCache[code] = evalled;
  },
  warnOnce: function (text) {
    if (!Runtime.warnOnce.shown) Runtime.warnOnce.shown = {};
    if (!Runtime.warnOnce.shown[text]) {
      Runtime.warnOnce.shown[text] = 1;
      Module.printErr(text);
    }
  },
  funcWrappers: {},
  getFuncWrapper: function (func, sig) {
    assert(sig);
    if (!Runtime.funcWrappers[func]) {
      Runtime.funcWrappers[func] = function dynCall_wrapper() {
        return Runtime.dynCall(sig, func, arguments);
      };
    }
    return Runtime.funcWrappers[func];
  },
  UTF8Processor: function () {
    var buffer = [];
    var needed = 0;
    this.processCChar = function (code) {
      code = code & 0xFF;

      if (buffer.length == 0) {
        if ((code & 0x80) == 0x00) {        // 0xxxxxxx
          return String.fromCharCode(code);
        }
        buffer.push(code);
        if ((code & 0xE0) == 0xC0) {        // 110xxxxx
          needed = 1;
        } else if ((code & 0xF0) == 0xE0) { // 1110xxxx
          needed = 2;
        } else {                            // 11110xxx
          needed = 3;
        }
        return '';
      }

      if (needed) {
        buffer.push(code);
        needed--;
        if (needed > 0) return '';
      }

      var c1 = buffer[0];
      var c2 = buffer[1];
      var c3 = buffer[2];
      var c4 = buffer[3];
      var ret;
      if (buffer.length == 2) {
        ret = String.fromCharCode(((c1 & 0x1F) << 6)  | (c2 & 0x3F));
      } else if (buffer.length == 3) {
        ret = String.fromCharCode(((c1 & 0x0F) << 12) | ((c2 & 0x3F) << 6)  | (c3 & 0x3F));
      } else {
        // http://mathiasbynens.be/notes/javascript-encoding#surrogate-formulae
        var codePoint = ((c1 & 0x07) << 18) | ((c2 & 0x3F) << 12) |
                        ((c3 & 0x3F) << 6)  | (c4 & 0x3F);
        ret = String.fromCharCode(
          Math.floor((codePoint - 0x10000) / 0x400) + 0xD800,
          (codePoint - 0x10000) % 0x400 + 0xDC00);
      }
      buffer.length = 0;
      return ret;
    }
    this.processJSString = function processJSString(string) {
      /* TODO: use TextEncoder when present,
        var encoder = new TextEncoder();
        encoder['encoding'] = "utf-8";
        var utf8Array = encoder['encode'](aMsg.data);
      */
      string = unescape(encodeURIComponent(string));
      var ret = [];
      for (var i = 0; i < string.length; i++) {
        ret.push(string.charCodeAt(i));
      }
      return ret;
    }
  },
  getCompilerSetting: function (name) {
    throw 'You must build with -s RETAIN_COMPILER_SETTINGS=1 for Runtime.getCompilerSetting or emscripten_get_compiler_setting to work';
  },
  stackAlloc: function (size) { var ret = STACKTOP;STACKTOP = (STACKTOP + size)|0;STACKTOP = (((STACKTOP)+7)&-8); return ret; },
  staticAlloc: function (size) { var ret = STATICTOP;STATICTOP = (STATICTOP + size)|0;STATICTOP = (((STATICTOP)+7)&-8); return ret; },
  dynamicAlloc: function (size) { var ret = DYNAMICTOP;DYNAMICTOP = (DYNAMICTOP + size)|0;DYNAMICTOP = (((DYNAMICTOP)+7)&-8); if (DYNAMICTOP >= TOTAL_MEMORY) enlargeMemory();; return ret; },
  alignMemory: function (size,quantum) { var ret = size = Math.ceil((size)/(quantum ? quantum : 8))*(quantum ? quantum : 8); return ret; },
  makeBigInt: function (low,high,unsigned) { var ret = (unsigned ? ((+((low>>>0)))+((+((high>>>0)))*(+4294967296))) : ((+((low>>>0)))+((+((high|0)))*(+4294967296)))); return ret; },
  GLOBAL_BASE: 8,
  QUANTUM_SIZE: 4,
  __dummy__: 0
}


Module['Runtime'] = Runtime;









//========================================
// Runtime essentials
//========================================

var __THREW__ = 0; // Used in checking for thrown exceptions.

var ABORT = false; // whether we are quitting the application. no code should run after this. set in exit() and abort()
var EXITSTATUS = 0;

var undef = 0;
// tempInt is used for 32-bit signed values or smaller. tempBigInt is used
// for 32-bit unsigned values or more than 32 bits. TODO: audit all uses of tempInt
var tempValue, tempInt, tempBigInt, tempInt2, tempBigInt2, tempPair, tempBigIntI, tempBigIntR, tempBigIntS, tempBigIntP, tempBigIntD, tempDouble, tempFloat;
var tempI64, tempI64b;
var tempRet0, tempRet1, tempRet2, tempRet3, tempRet4, tempRet5, tempRet6, tempRet7, tempRet8, tempRet9;

function assert(condition, text) {
  if (!condition) {
    abort('Assertion failed: ' + text);
  }
}

var globalScope = this;

// C calling interface. A convenient way to call C functions (in C files, or
// defined with extern "C").
//
// Note: LLVM optimizations can inline and remove functions, after which you will not be
//       able to call them. Closure can also do so. To avoid that, add your function to
//       the exports using something like
//
//         -s EXPORTED_FUNCTIONS='["_main", "_myfunc"]'
//
// @param ident      The name of the C function (note that C++ functions will be name-mangled - use extern "C")
// @param returnType The return type of the function, one of the JS types 'number', 'string' or 'array' (use 'number' for any C pointer, and
//                   'array' for JavaScript arrays and typed arrays; note that arrays are 8-bit).
// @param argTypes   An array of the types of arguments for the function (if there are no arguments, this can be ommitted). Types are as in returnType,
//                   except that 'array' is not possible (there is no way for us to know the length of the array)
// @param args       An array of the arguments to the function, as native JS values (as in returnType)
//                   Note that string arguments will be stored on the stack (the JS string will become a C string on the stack).
// @return           The return value, as a native JS value (as in returnType)
function ccall(ident, returnType, argTypes, args) {
  return ccallFunc(getCFunc(ident), returnType, argTypes, args);
}
Module["ccall"] = ccall;

// Returns the C function with a specified identifier (for C++, you need to do manual name mangling)
function getCFunc(ident) {
  try {
    var func = Module['_' + ident]; // closure exported function
    if (!func) func = eval('_' + ident); // explicit lookup
  } catch(e) {
  }
  assert(func, 'Cannot call unknown function ' + ident + ' (perhaps LLVM optimizations or closure removed it?)');
  return func;
}

// Internal function that does a C call using a function, not an identifier
function ccallFunc(func, returnType, argTypes, args) {
  var stack = 0;
  function toC(value, type) {
    if (type == 'string') {
      if (value === null || value === undefined || value === 0) return 0; // null string
      value = intArrayFromString(value);
      type = 'array';
    }
    if (type == 'array') {
      if (!stack) stack = Runtime.stackSave();
      var ret = Runtime.stackAlloc(value.length);
      writeArrayToMemory(value, ret);
      return ret;
    }
    return value;
  }
  function fromC(value, type) {
    if (type == 'string') {
      return Pointer_stringify(value);
    }
    assert(type != 'array');
    return value;
  }
  var i = 0;
  var cArgs = args ? args.map(function(arg) {
    return toC(arg, argTypes[i++]);
  }) : [];
  var ret = fromC(func.apply(null, cArgs), returnType);
  if (stack) Runtime.stackRestore(stack);
  return ret;
}

// Returns a native JS wrapper for a C function. This is similar to ccall, but
// returns a function you can call repeatedly in a normal way. For example:
//
//   var my_function = cwrap('my_c_function', 'number', ['number', 'number']);
//   alert(my_function(5, 22));
//   alert(my_function(99, 12));
//
function cwrap(ident, returnType, argTypes) {
  var func = getCFunc(ident);
  return function() {
    return ccallFunc(func, returnType, argTypes, Array.prototype.slice.call(arguments));
  }
}
Module["cwrap"] = cwrap;

// Sets a value in memory in a dynamic way at run-time. Uses the
// type data. This is the same as makeSetValue, except that
// makeSetValue is done at compile-time and generates the needed
// code then, whereas this function picks the right code at
// run-time.
// Note that setValue and getValue only do *aligned* writes and reads!
// Note that ccall uses JS types as for defining types, while setValue and
// getValue need LLVM types ('i8', 'i32') - this is a lower-level operation
function setValue(ptr, value, type, noSafe) {
  type = type || 'i8';
  if (type.charAt(type.length-1) === '*') type = 'i32'; // pointers are 32-bit
    switch(type) {
      case 'i1': HEAP8[(ptr)]=value; break;
      case 'i8': HEAP8[(ptr)]=value; break;
      case 'i16': HEAP16[((ptr)>>1)]=value; break;
      case 'i32': HEAP32[((ptr)>>2)]=value; break;
      case 'i64': (tempI64 = [value>>>0,(tempDouble=value,(+(Math_abs(tempDouble))) >= (+1) ? (tempDouble > (+0) ? ((Math_min((+(Math_floor((tempDouble)/(+4294967296)))), (+4294967295)))|0)>>>0 : (~~((+(Math_ceil((tempDouble - +(((~~(tempDouble)))>>>0))/(+4294967296))))))>>>0) : 0)],HEAP32[((ptr)>>2)]=tempI64[0],HEAP32[(((ptr)+(4))>>2)]=tempI64[1]); break;
      case 'float': HEAPF32[((ptr)>>2)]=value; break;
      case 'double': HEAPF64[((ptr)>>3)]=value; break;
      default: abort('invalid type for setValue: ' + type);
    }
}
Module['setValue'] = setValue;

// Parallel to setValue.
function getValue(ptr, type, noSafe) {
  type = type || 'i8';
  if (type.charAt(type.length-1) === '*') type = 'i32'; // pointers are 32-bit
    switch(type) {
      case 'i1': return HEAP8[(ptr)];
      case 'i8': return HEAP8[(ptr)];
      case 'i16': return HEAP16[((ptr)>>1)];
      case 'i32': return HEAP32[((ptr)>>2)];
      case 'i64': return HEAP32[((ptr)>>2)];
      case 'float': return HEAPF32[((ptr)>>2)];
      case 'double': return HEAPF64[((ptr)>>3)];
      default: abort('invalid type for setValue: ' + type);
    }
  return null;
}
Module['getValue'] = getValue;

var ALLOC_NORMAL = 0; // Tries to use _malloc()
var ALLOC_STACK = 1; // Lives for the duration of the current function call
var ALLOC_STATIC = 2; // Cannot be freed
var ALLOC_DYNAMIC = 3; // Cannot be freed except through sbrk
var ALLOC_NONE = 4; // Do not allocate
Module['ALLOC_NORMAL'] = ALLOC_NORMAL;
Module['ALLOC_STACK'] = ALLOC_STACK;
Module['ALLOC_STATIC'] = ALLOC_STATIC;
Module['ALLOC_DYNAMIC'] = ALLOC_DYNAMIC;
Module['ALLOC_NONE'] = ALLOC_NONE;

// allocate(): This is for internal use. You can use it yourself as well, but the interface
//             is a little tricky (see docs right below). The reason is that it is optimized
//             for multiple syntaxes to save space in generated code. So you should
//             normally not use allocate(), and instead allocate memory using _malloc(),
//             initialize it with setValue(), and so forth.
// @slab: An array of data, or a number. If a number, then the size of the block to allocate,
//        in *bytes* (note that this is sometimes confusing: the next parameter does not
//        affect this!)
// @types: Either an array of types, one for each byte (or 0 if no type at that position),
//         or a single type which is used for the entire block. This only matters if there
//         is initial data - if @slab is a number, then this does not matter at all and is
//         ignored.
// @allocator: How to allocate memory, see ALLOC_*
function allocate(slab, types, allocator, ptr) {
  var zeroinit, size;
  if (typeof slab === 'number') {
    zeroinit = true;
    size = slab;
  } else {
    zeroinit = false;
    size = slab.length;
  }

  var singleType = typeof types === 'string' ? types : null;

  var ret;
  if (allocator == ALLOC_NONE) {
    ret = ptr;
  } else {
    ret = [_malloc, Runtime.stackAlloc, Runtime.staticAlloc, Runtime.dynamicAlloc][allocator === undefined ? ALLOC_STATIC : allocator](Math.max(size, singleType ? 1 : types.length));
  }

  if (zeroinit) {
    var ptr = ret, stop;
    assert((ret & 3) == 0);
    stop = ret + (size & ~3);
    for (; ptr < stop; ptr += 4) {
      HEAP32[((ptr)>>2)]=0;
    }
    stop = ret + size;
    while (ptr < stop) {
      HEAP8[((ptr++)|0)]=0;
    }
    return ret;
  }

  if (singleType === 'i8') {
    if (slab.subarray || slab.slice) {
      HEAPU8.set(slab, ret);
    } else {
      HEAPU8.set(new Uint8Array(slab), ret);
    }
    return ret;
  }

  var i = 0, type, typeSize, previousType;
  while (i < size) {
    var curr = slab[i];

    if (typeof curr === 'function') {
      curr = Runtime.getFunctionIndex(curr);
    }

    type = singleType || types[i];
    if (type === 0) {
      i++;
      continue;
    }

    if (type == 'i64') type = 'i32'; // special case: we have one i32 here, and one i32 later

    setValue(ret+i, curr, type);

    // no need to look up size unless type changes, so cache it
    if (previousType !== type) {
      typeSize = Runtime.getNativeTypeSize(type);
      previousType = type;
    }
    i += typeSize;
  }

  return ret;
}
Module['allocate'] = allocate;

function Pointer_stringify(ptr, /* optional */ length) {
  // TODO: use TextDecoder
  // Find the length, and check for UTF while doing so
  var hasUtf = false;
  var t;
  var i = 0;
  while (1) {
    t = HEAPU8[(((ptr)+(i))|0)];
    if (t >= 128) hasUtf = true;
    else if (t == 0 && !length) break;
    i++;
    if (length && i == length) break;
  }
  if (!length) length = i;

  var ret = '';

  if (!hasUtf) {
    var MAX_CHUNK = 1024; // split up into chunks, because .apply on a huge string can overflow the stack
    var curr;
    while (length > 0) {
      curr = String.fromCharCode.apply(String, HEAPU8.subarray(ptr, ptr + Math.min(length, MAX_CHUNK)));
      ret = ret ? ret + curr : curr;
      ptr += MAX_CHUNK;
      length -= MAX_CHUNK;
    }
    return ret;
  }

  var utf8 = new Runtime.UTF8Processor();
  for (i = 0; i < length; i++) {
    t = HEAPU8[(((ptr)+(i))|0)];
    ret += utf8.processCChar(t);
  }
  return ret;
}
Module['Pointer_stringify'] = Pointer_stringify;

// Given a pointer 'ptr' to a null-terminated UTF16LE-encoded string in the emscripten HEAP, returns
// a copy of that string as a Javascript String object.
function UTF16ToString(ptr) {
  var i = 0;

  var str = '';
  while (1) {
    var codeUnit = HEAP16[(((ptr)+(i*2))>>1)];
    if (codeUnit == 0)
      return str;
    ++i;
    // fromCharCode constructs a character from a UTF-16 code unit, so we can pass the UTF16 string right through.
    str += String.fromCharCode(codeUnit);
  }
}
Module['UTF16ToString'] = UTF16ToString;

// Copies the given Javascript String object 'str' to the emscripten HEAP at address 'outPtr',
// null-terminated and encoded in UTF16LE form. The copy will require at most (str.length*2+1)*2 bytes of space in the HEAP.
function stringToUTF16(str, outPtr) {
  for(var i = 0; i < str.length; ++i) {
    // charCodeAt returns a UTF-16 encoded code unit, so it can be directly written to the HEAP.
    var codeUnit = str.charCodeAt(i); // possibly a lead surrogate
    HEAP16[(((outPtr)+(i*2))>>1)]=codeUnit;
  }
  // Null-terminate the pointer to the HEAP.
  HEAP16[(((outPtr)+(str.length*2))>>1)]=0;
}
Module['stringToUTF16'] = stringToUTF16;

// Given a pointer 'ptr' to a null-terminated UTF32LE-encoded string in the emscripten HEAP, returns
// a copy of that string as a Javascript String object.
function UTF32ToString(ptr) {
  var i = 0;

  var str = '';
  while (1) {
    var utf32 = HEAP32[(((ptr)+(i*4))>>2)];
    if (utf32 == 0)
      return str;
    ++i;
    // Gotcha: fromCharCode constructs a character from a UTF-16 encoded code (pair), not from a Unicode code point! So encode the code point to UTF-16 for constructing.
    if (utf32 >= 0x10000) {
      var ch = utf32 - 0x10000;
      str += String.fromCharCode(0xD800 | (ch >> 10), 0xDC00 | (ch & 0x3FF));
    } else {
      str += String.fromCharCode(utf32);
    }
  }
}
Module['UTF32ToString'] = UTF32ToString;

// Copies the given Javascript String object 'str' to the emscripten HEAP at address 'outPtr',
// null-terminated and encoded in UTF32LE form. The copy will require at most (str.length+1)*4 bytes of space in the HEAP,
// but can use less, since str.length does not return the number of characters in the string, but the number of UTF-16 code units in the string.
function stringToUTF32(str, outPtr) {
  var iChar = 0;
  for(var iCodeUnit = 0; iCodeUnit < str.length; ++iCodeUnit) {
    // Gotcha: charCodeAt returns a 16-bit word that is a UTF-16 encoded code unit, not a Unicode code point of the character! We must decode the string to UTF-32 to the heap.
    var codeUnit = str.charCodeAt(iCodeUnit); // possibly a lead surrogate
    if (codeUnit >= 0xD800 && codeUnit <= 0xDFFF) {
      var trailSurrogate = str.charCodeAt(++iCodeUnit);
      codeUnit = 0x10000 + ((codeUnit & 0x3FF) << 10) | (trailSurrogate & 0x3FF);
    }
    HEAP32[(((outPtr)+(iChar*4))>>2)]=codeUnit;
    ++iChar;
  }
  // Null-terminate the pointer to the HEAP.
  HEAP32[(((outPtr)+(iChar*4))>>2)]=0;
}
Module['stringToUTF32'] = stringToUTF32;

function demangle(func) {
  var i = 3;
  // params, etc.
  var basicTypes = {
    'v': 'void',
    'b': 'bool',
    'c': 'char',
    's': 'short',
    'i': 'int',
    'l': 'long',
    'f': 'float',
    'd': 'double',
    'w': 'wchar_t',
    'a': 'signed char',
    'h': 'unsigned char',
    't': 'unsigned short',
    'j': 'unsigned int',
    'm': 'unsigned long',
    'x': 'long long',
    'y': 'unsigned long long',
    'z': '...'
  };
  var subs = [];
  var first = true;
  function dump(x) {
    //return;
    if (x) Module.print(x);
    Module.print(func);
    var pre = '';
    for (var a = 0; a < i; a++) pre += ' ';
    Module.print (pre + '^');
  }
  function parseNested() {
    i++;
    if (func[i] === 'K') i++; // ignore const
    var parts = [];
    while (func[i] !== 'E') {
      if (func[i] === 'S') { // substitution
        i++;
        var next = func.indexOf('_', i);
        var num = func.substring(i, next) || 0;
        parts.push(subs[num] || '?');
        i = next+1;
        continue;
      }
      if (func[i] === 'C') { // constructor
        parts.push(parts[parts.length-1]);
        i += 2;
        continue;
      }
      var size = parseInt(func.substr(i));
      var pre = size.toString().length;
      if (!size || !pre) { i--; break; } // counter i++ below us
      var curr = func.substr(i + pre, size);
      parts.push(curr);
      subs.push(curr);
      i += pre + size;
    }
    i++; // skip E
    return parts;
  }
  function parse(rawList, limit, allowVoid) { // main parser
    limit = limit || Infinity;
    var ret = '', list = [];
    function flushList() {
      return '(' + list.join(', ') + ')';
    }
    var name;
    if (func[i] === 'N') {
      // namespaced N-E
      name = parseNested().join('::');
      limit--;
      if (limit === 0) return rawList ? [name] : name;
    } else {
      // not namespaced
      if (func[i] === 'K' || (first && func[i] === 'L')) i++; // ignore const and first 'L'
      var size = parseInt(func.substr(i));
      if (size) {
        var pre = size.toString().length;
        name = func.substr(i + pre, size);
        i += pre + size;
      }
    }
    first = false;
    if (func[i] === 'I') {
      i++;
      var iList = parse(true);
      var iRet = parse(true, 1, true);
      ret += iRet[0] + ' ' + name + '<' + iList.join(', ') + '>';
    } else {
      ret = name;
    }
    paramLoop: while (i < func.length && limit-- > 0) {
      //dump('paramLoop');
      var c = func[i++];
      if (c in basicTypes) {
        list.push(basicTypes[c]);
      } else {
        switch (c) {
          case 'P': list.push(parse(true, 1, true)[0] + '*'); break; // pointer
          case 'R': list.push(parse(true, 1, true)[0] + '&'); break; // reference
          case 'L': { // literal
            i++; // skip basic type
            var end = func.indexOf('E', i);
            var size = end - i;
            list.push(func.substr(i, size));
            i += size + 2; // size + 'EE'
            break;
          }
          case 'A': { // array
            var size = parseInt(func.substr(i));
            i += size.toString().length;
            if (func[i] !== '_') throw '?';
            i++; // skip _
            list.push(parse(true, 1, true)[0] + ' [' + size + ']');
            break;
          }
          case 'E': break paramLoop;
          default: ret += '?' + c; break paramLoop;
        }
      }
    }
    if (!allowVoid && list.length === 1 && list[0] === 'void') list = []; // avoid (void)
    if (rawList) {
      if (ret) {
        list.push(ret + '?');
      }
      return list;
    } else {
      return ret + flushList();
    }
  }
  try {
    // Special-case the entry point, since its name differs from other name mangling.
    if (func == 'Object._main' || func == '_main') {
      return 'main()';
    }
    if (typeof func === 'number') func = Pointer_stringify(func);
    if (func[0] !== '_') return func;
    if (func[1] !== '_') return func; // C function
    if (func[2] !== 'Z') return func;
    switch (func[3]) {
      case 'n': return 'operator new()';
      case 'd': return 'operator delete()';
    }
    return parse();
  } catch(e) {
    return func;
  }
}

function demangleAll(text) {
  return text.replace(/__Z[\w\d_]+/g, function(x) { var y = demangle(x); return x === y ? x : (x + ' [' + y + ']') });
}

function stackTrace() {
  var stack = new Error().stack;
  return stack ? demangleAll(stack) : '(no stack trace available)'; // Stack trace is not available at least on IE10 and Safari 6.
}

// Memory management

var PAGE_SIZE = 4096;
function alignMemoryPage(x) {
  return (x+4095)&-4096;
}

var HEAP;
var HEAP8, HEAPU8, HEAP16, HEAPU16, HEAP32, HEAPU32, HEAPF32, HEAPF64;

var STATIC_BASE = 0, STATICTOP = 0, staticSealed = false; // static area
var STACK_BASE = 0, STACKTOP = 0, STACK_MAX = 0; // stack area
var DYNAMIC_BASE = 0, DYNAMICTOP = 0; // dynamic area handled by sbrk

function enlargeMemory() {
  abort('Cannot enlarge memory arrays. Either (1) compile with -s TOTAL_MEMORY=X with X higher than the current value ' + TOTAL_MEMORY + ', (2) compile with ALLOW_MEMORY_GROWTH which adjusts the size at runtime but prevents some optimizations, or (3) set Module.TOTAL_MEMORY before the program runs.');
}

var TOTAL_STACK = Module['TOTAL_STACK'] || 5242880;
var TOTAL_MEMORY = Module['TOTAL_MEMORY'] || 16777216;
var FAST_MEMORY = Module['FAST_MEMORY'] || 2097152;

var totalMemory = 4096;
while (totalMemory < TOTAL_MEMORY || totalMemory < 2*TOTAL_STACK) {
  if (totalMemory < 16*1024*1024) {
    totalMemory *= 2;
  } else {
    totalMemory += 16*1024*1024
  }
}
if (totalMemory !== TOTAL_MEMORY) {
  Module.printErr('increasing TOTAL_MEMORY to ' + totalMemory + ' to be more reasonable');
  TOTAL_MEMORY = totalMemory;
}

// Initialize the runtime's memory
// check for full engine support (use string 'subarray' to avoid closure compiler confusion)
assert(typeof Int32Array !== 'undefined' && typeof Float64Array !== 'undefined' && !!(new Int32Array(1)['subarray']) && !!(new Int32Array(1)['set']),
       'JS engine does not provide full typed array support');

var buffer = new ArrayBuffer(TOTAL_MEMORY);
HEAP8 = new Int8Array(buffer);
HEAP16 = new Int16Array(buffer);
HEAP32 = new Int32Array(buffer);
HEAPU8 = new Uint8Array(buffer);
HEAPU16 = new Uint16Array(buffer);
HEAPU32 = new Uint32Array(buffer);
HEAPF32 = new Float32Array(buffer);
HEAPF64 = new Float64Array(buffer);

// Endianness check (note: assumes compiler arch was little-endian)
HEAP32[0] = 255;
assert(HEAPU8[0] === 255 && HEAPU8[3] === 0, 'Typed arrays 2 must be run on a little-endian system');

Module['HEAP'] = HEAP;
Module['HEAP8'] = HEAP8;
Module['HEAP16'] = HEAP16;
Module['HEAP32'] = HEAP32;
Module['HEAPU8'] = HEAPU8;
Module['HEAPU16'] = HEAPU16;
Module['HEAPU32'] = HEAPU32;
Module['HEAPF32'] = HEAPF32;
Module['HEAPF64'] = HEAPF64;

function callRuntimeCallbacks(callbacks) {
  while(callbacks.length > 0) {
    var callback = callbacks.shift();
    if (typeof callback == 'function') {
      callback();
      continue;
    }
    var func = callback.func;
    if (typeof func === 'number') {
      if (callback.arg === undefined) {
        Runtime.dynCall('v', func);
      } else {
        Runtime.dynCall('vi', func, [callback.arg]);
      }
    } else {
      func(callback.arg === undefined ? null : callback.arg);
    }
  }
}

var __ATPRERUN__  = []; // functions called before the runtime is initialized
var __ATINIT__    = []; // functions called during startup
var __ATMAIN__    = []; // functions called when main() is to be run
var __ATEXIT__    = []; // functions called during shutdown
var __ATPOSTRUN__ = []; // functions called after the runtime has exited

var runtimeInitialized = false;

function preRun() {
  // compatibility - merge in anything from Module['preRun'] at this time
  if (Module['preRun']) {
    if (typeof Module['preRun'] == 'function') Module['preRun'] = [Module['preRun']];
    while (Module['preRun'].length) {
      addOnPreRun(Module['preRun'].shift());
    }
  }
  callRuntimeCallbacks(__ATPRERUN__);
}

function ensureInitRuntime() {
  if (runtimeInitialized) return;
  runtimeInitialized = true;
  callRuntimeCallbacks(__ATINIT__);
}

function preMain() {
  callRuntimeCallbacks(__ATMAIN__);
}

function exitRuntime() {
  callRuntimeCallbacks(__ATEXIT__);
}

function postRun() {
  // compatibility - merge in anything from Module['postRun'] at this time
  if (Module['postRun']) {
    if (typeof Module['postRun'] == 'function') Module['postRun'] = [Module['postRun']];
    while (Module['postRun'].length) {
      addOnPostRun(Module['postRun'].shift());
    }
  }
  callRuntimeCallbacks(__ATPOSTRUN__);
}

function addOnPreRun(cb) {
  __ATPRERUN__.unshift(cb);
}
Module['addOnPreRun'] = Module.addOnPreRun = addOnPreRun;

function addOnInit(cb) {
  __ATINIT__.unshift(cb);
}
Module['addOnInit'] = Module.addOnInit = addOnInit;

function addOnPreMain(cb) {
  __ATMAIN__.unshift(cb);
}
Module['addOnPreMain'] = Module.addOnPreMain = addOnPreMain;

function addOnExit(cb) {
  __ATEXIT__.unshift(cb);
}
Module['addOnExit'] = Module.addOnExit = addOnExit;

function addOnPostRun(cb) {
  __ATPOSTRUN__.unshift(cb);
}
Module['addOnPostRun'] = Module.addOnPostRun = addOnPostRun;

// Tools

// This processes a JS string into a C-line array of numbers, 0-terminated.
// For LLVM-originating strings, see parser.js:parseLLVMString function
function intArrayFromString(stringy, dontAddNull, length /* optional */) {
  var ret = (new Runtime.UTF8Processor()).processJSString(stringy);
  if (length) {
    ret.length = length;
  }
  if (!dontAddNull) {
    ret.push(0);
  }
  return ret;
}
Module['intArrayFromString'] = intArrayFromString;

function intArrayToString(array) {
  var ret = [];
  for (var i = 0; i < array.length; i++) {
    var chr = array[i];
    if (chr > 0xFF) {
      chr &= 0xFF;
    }
    ret.push(String.fromCharCode(chr));
  }
  return ret.join('');
}
Module['intArrayToString'] = intArrayToString;

// Write a Javascript array to somewhere in the heap
function writeStringToMemory(string, buffer, dontAddNull) {
  var array = intArrayFromString(string, dontAddNull);
  var i = 0;
  while (i < array.length) {
    var chr = array[i];
    HEAP8[(((buffer)+(i))|0)]=chr;
    i = i + 1;
  }
}
Module['writeStringToMemory'] = writeStringToMemory;

function writeArrayToMemory(array, buffer) {
  for (var i = 0; i < array.length; i++) {
    HEAP8[(((buffer)+(i))|0)]=array[i];
  }
}
Module['writeArrayToMemory'] = writeArrayToMemory;

function writeAsciiToMemory(str, buffer, dontAddNull) {
  for (var i = 0; i < str.length; i++) {
    HEAP8[(((buffer)+(i))|0)]=str.charCodeAt(i);
  }
  if (!dontAddNull) HEAP8[(((buffer)+(str.length))|0)]=0;
}
Module['writeAsciiToMemory'] = writeAsciiToMemory;

function unSign(value, bits, ignore) {
  if (value >= 0) {
    return value;
  }
  return bits <= 32 ? 2*Math.abs(1 << (bits-1)) + value // Need some trickery, since if bits == 32, we are right at the limit of the bits JS uses in bitshifts
                    : Math.pow(2, bits)         + value;
}
function reSign(value, bits, ignore) {
  if (value <= 0) {
    return value;
  }
  var half = bits <= 32 ? Math.abs(1 << (bits-1)) // abs is needed if bits == 32
                        : Math.pow(2, bits-1);
  if (value >= half && (bits <= 32 || value > half)) { // for huge values, we can hit the precision limit and always get true here. so don't do that
                                                       // but, in general there is no perfect solution here. With 64-bit ints, we get rounding and errors
                                                       // TODO: In i64 mode 1, resign the two parts separately and safely
    value = -2*half + value; // Cannot bitshift half, as it may be at the limit of the bits JS uses in bitshifts
  }
  return value;
}

// check for imul support, and also for correctness ( https://bugs.webkit.org/show_bug.cgi?id=126345 )
if (!Math['imul'] || Math['imul'](0xffffffff, 5) !== -5) Math['imul'] = function imul(a, b) {
  var ah  = a >>> 16;
  var al = a & 0xffff;
  var bh  = b >>> 16;
  var bl = b & 0xffff;
  return (al*bl + ((ah*bl + al*bh) << 16))|0;
};
Math.imul = Math['imul'];


var Math_abs = Math.abs;
var Math_cos = Math.cos;
var Math_sin = Math.sin;
var Math_tan = Math.tan;
var Math_acos = Math.acos;
var Math_asin = Math.asin;
var Math_atan = Math.atan;
var Math_atan2 = Math.atan2;
var Math_exp = Math.exp;
var Math_log = Math.log;
var Math_sqrt = Math.sqrt;
var Math_ceil = Math.ceil;
var Math_floor = Math.floor;
var Math_pow = Math.pow;
var Math_imul = Math.imul;
var Math_fround = Math.fround;
var Math_min = Math.min;

// A counter of dependencies for calling run(). If we need to
// do asynchronous work before running, increment this and
// decrement it. Incrementing must happen in a place like
// PRE_RUN_ADDITIONS (used by emcc to add file preloading).
// Note that you can add dependencies in preRun, even though
// it happens right before run - run will be postponed until
// the dependencies are met.
var runDependencies = 0;
var runDependencyWatcher = null;
var dependenciesFulfilled = null; // overridden to take different actions when all run dependencies are fulfilled

function addRunDependency(id) {
  runDependencies++;
  if (Module['monitorRunDependencies']) {
    Module['monitorRunDependencies'](runDependencies);
  }
}
Module['addRunDependency'] = addRunDependency;
function removeRunDependency(id) {
  runDependencies--;
  if (Module['monitorRunDependencies']) {
    Module['monitorRunDependencies'](runDependencies);
  }
  if (runDependencies == 0) {
    if (runDependencyWatcher !== null) {
      clearInterval(runDependencyWatcher);
      runDependencyWatcher = null;
    }
    if (dependenciesFulfilled) {
      var callback = dependenciesFulfilled;
      dependenciesFulfilled = null;
      callback(); // can add another dependenciesFulfilled
    }
  }
}
Module['removeRunDependency'] = removeRunDependency;

Module["preloadedImages"] = {}; // maps url to image data
Module["preloadedAudios"] = {}; // maps url to audio data


var memoryInitializer = null;

// === Body ===





STATIC_BASE = 8;

STATICTOP = STATIC_BASE + Runtime.alignMemory(6491);
/* global initializers */ __ATINIT__.push();


/* memory initializer */ allocate([100,114,97,119,105,110,103,46,99,0,0,0,0,0,0,0,100,114,45,62,109,101,0,0,115,116,97,116,117,115,95,98,97,114,0,0,0,0,0,0,105,110,100,101,120,32,62,61,32,48,0,0,0,0,0,0,100,115,102,46,99,0,0,0,101,100,115,102,95,99,97,110,111,110,105,102,121,0,0,0,105,110,118,101,114,115,101,32,61,61,32,48,0,0,0,0,100,115,102,91,118,49,93,32,38,32,50,0,0,0,0,0,101,100,115,102,95,109,101,114,103,101,0,0,0,0,0,0,100,115,102,91,118,50,93,32,38,32,50,0,0,0,0,0,33,105,110,118,101,114,115,101,0,0,0,0,0,0,0,0,105,110,118,101,114,115,101,32,61,61,32,48,32,124,124,32,105,110,118,101,114,115,101,32,61,61,32,49,0,0,0,0,118,50,32,61,61,32,118,49,0,0,0,0,0,0,0,0,105,50,32,61,61,32,105,110,118,101,114,115,101,0,0,0,103,45,62,114,101,102,99,111,117,110,116,0,0,0,0,0,103,114,105,100,46,99,0,0,103,114,105,100,95,102,114,101,101,0,0,0,0,0,0,0,98,101,115,116,100,105,115,116,32,62,32,48,0,0,0,0,103,114,105,100,95,102,105,110,100,95,105,110,99,101,110,116,114,101,0,0,0,0,0,0,48,0,0,0,0,0,0,0,71,114,105,100,32,100,101,115,99,114,105,112,116,105,111,110,32,115,116,114,105,110,103,115,32,110,111,116,32,117,115,101,100,32,119,105,116,104,32,116,104,105,115,32,103,114,105,100,32,116,121,112,101,0,0,0,33,34,73,110,118,97,108,105,100,32,103,114,105,100,32,100,101,115,99,114,105,112,116,105,111,110,46,34,0,0,0,0,103,114,105,100,95,110,101,119,0,0,0,0,0,0,0,0,1,0,0,0,2,0,0,0,3,0,0,0,4,0,0,0,5,0,0,0,6,0,0,0,7,0,0,0,8,0,0,0,9,0,0,0,10,0,0,0,11,0,0,0,12,0,0,0,13,0,0,0,0,0,0,0,1,0,0,0,2,0,0,0,3,0,0,0,4,0,0,0,5,0,0,0,6,0,0,0,7,0,0,0,8,0,0,0,9,0,0,0,10,0,0,0,11,0,0,0,12,0,0,0,13,0,0,0,0,0,0,0,71,37,100,44,37,100,44,37,100,0,0,0,0,0,0,0,103,114,105,100,95,110,101,119,95,112,101,110,114,111,115,101,0,0,0,0,0,0,0,0,103,45,62,110,117,109,95,102,97,99,101,115,32,60,61,32,109,97,120,95,102,97,99,101,115,0,0,0,0,0,0,0,103,45,62,110,117,109,95,100,111,116,115,32,60,61,32,109,97,120,95,100,111,116,115,0,110,101,120,116,95,110,101,119,95,101,100,103,101,32,45,32,103,45,62,101,100,103,101,115,32,60,32,103,45,62,110,117,109,95,101,100,103,101,115,0,103,114,105,100,95,109,97,107,101,95,99,111,110,115,105,115,116,101,110,116,0,0,0,0,107,32,33,61,32,102,45,62,111,114,100,101,114,0,0,0,102,45,62,101,100,103,101,115,91,107,93,32,61,61,32,78,85,76,76,0,0,0,0,0,102,45,62,101,100,103,101,115,91,107,50,93,32,61,61,32,78,85,76,76,0,0,0,0,33,34,71,114,105,100,32,98,114,111,107,101,110,58,32,98,97,100,32,101,100,103,101,45,102,97,99,101,32,114,101,108,97,116,105,111,110,115,104,105,112,34,0,0,0,0,0,0,100,45,62,111,114,100,101,114,32,62,61,32,50,0,0,0,102,32,33,61,32,78,85,76,76,0,0,0,0,0,0,0,106,32,33,61,32,102,45,62,111,114,100,101,114,0,0,0,100,45,62,102,97,99,101,115,91,99,117,114,114,101,110,116,95,102,97,99,101,50,93,0,103,114,105,100,95,110,101,119,95,103,114,101,97,116,100,111,100,101,99,97,103,111,110,97,108,0,0,0,0,0,0,0,103,114,105,100,95,110,101,119,95,100,111,100,101,99,97,103,111,110,97,108,0,0,0,0,103,114,105,100,95,110,101,119,95,102,108,111,114,101,116,0,103,114,105,100,95,110,101,119,95,107,105,116,101,115,0,0,103,114,105,100,95,110,101,119,95,111,99,116,97,103,111,110,97,108,0,0,0,0,0,0,103,114,105,100,95,110,101,119,95,103,114,101,97,116,104,101,120,97,103,111,110,97,108,0,103,114,105,100,95,110,101,119,95,99,97,105,114,111,0,0,103,114,105,100,95,110,101,119,95,115,110,117,98,115,113,117,97,114,101,0,0,0,0,0,103,114,105,100,95,110,101,119,95,116,114,105,97,110,103,117,108,97,114,0,0,0,0,0,103,114,105,100,95,110,101,119,95,104,111,110,101,121,99,111,109,98,0,0,0,0,0,0,103,114,105,100,95,110,101,119,95,115,113,117,97,114,101,0,85,110,114,101,99,111,103,110,105,115,101,100,32,103,114,105,100,32,100,101,115,99,114,105,112,116,105,111,110,46,0,0,77,105,115,115,105,110,103,32,103,114,105,100,32,100,101,115,99,114,105,112,116,105,111,110,32,115,116,114,105,110,103,46,0,0,0,0,0,0,0,0,73,110,118,97,108,105,100,32,102,111,114,109,97,116,32,103,114,105,100,32,100,101,115,99,114,105,112,116,105,111,110,32,115,116,114,105,110,103,46,0,80,97,116,99,104,32,111,102,102,115,101,116,32,111,117,116,32,111,102,32,98,111,117,110,100,115,46,0,0,0,0,0,65,110,103,108,101,32,111,102,102,115,101,116,32,111,117,116,32,111,102,32,98,111,117,110,100,115,46,0,0,0,0,0,80,97,116,99,104,32,99,111,111,114,100,105,110,97,116,101,115,32,100,111,32,110,111,116,32,105,100,101,110,116,105,102,121,32,97,32,117,115,97,98,108,101,32,103,114,105,100,32,102,114,97,103,109,101,110,116,0,0,0,0,0,0,0,0,112,117,122,122,108,101,32,102,97,116,97,108,32,101,114,114,111,114,58,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,66,97,99,107,115,112,97,99,101,0,0,0,0,0,0,0,68,101,108,0,0,0,0,0,69,110,116,101,114,0,0,0,76,101,102,116,0,0,0,0,85,112,0,0,0,0,0,0,82,105,103,104,116,0,0,0,68,111,119,110,0,0,0,0,69,110,100,0,0,0,0,0,80,97,103,101,68,111,119,110,0,0,0,0,0,0,0,0,72,111,109,101,0,0,0,0,80,97,103,101,85,112,0,0,1,0,0,0,1,0,0,0,2,0,0,0,14,0,0,0,3,0,0,0,15,0,0,0,16,0,0,0,1,0,0,0,2,0,0,0,3,0,0,0,1,0,0,0,14,0,0,0,2,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,105,32,60,32,110,112,114,101,115,101,116,115,0,0,0,0,101,109,99,99,46,99,0,0,99,111,109,109,97,110,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,35,37,48,50,120,37,48,50,120,37,48,50,120,0,0,0,0,0,0,0,0,0,0,0,37,100,112,120,32,37,115,0,109,111,110,111,115,112,97,99,101,0,0,0,0,0,0,0,115,97,110,115,45,115,101,114,105,102,0,0,0,0,0,0,99,95,108,105,103,104,116,97,98,108,101,32,33,61,32,48,32,38,38,32,99,95,100,97,114,107,97,98,108,101,32,33,61,32,48,0,0,0,0,0,108,111,111,112,103,101,110,46,99,0,0,0,0,0,0,0,103,101,110,101,114,97,116,101,95,108,111,111,112,0,0,0,102,115,0,0,0,0,0,0,98,111,97,114,100,91,107,93,32,61,61,32,70,65,67,69,95,71,82,69,89,0,0,0,98,111,97,114,100,91,105,93,32,61,61,32,70,65,67,69,95,71,82,69,89,0,0,0,98,111,97,114,100,91,102,97,99,101,95,105,110,100,101,120,93,32,33,61,32,99,111,108,111,117,114,0,0,0,0,0,99,97,110,95,99,111,108,111,117,114,95,102,97,99,101,0,106,32,33,61,32,116,101,115,116,95,102,97,99,101,45,62,100,111,116,115,91,105,93,45,62,111,114,100,101,114,0,0,76,111,111,112,121,0,0,0,103,97,109,101,115,46,108,111,111,112,121,0,0,0,0,0,108,111,111,112,121,0,0,0,184,7,0,0,192,7,0,0,208,7,0,0,1,0,0,0,16,0,0,0,3,0,0,0,1,0,0,0,4,0,0,0,1,0,0,0,1,0,0,0,2,0,0,0,3,0,0,0,2,0,0,0,1,0,0,0,3,0,0,0,17,0,0,0,4,0,0,0,5,0,0,0,1,0,0,0,2,0,0,0,1,0,0,0,5,0,0,0,6,0,0,0,7,0,0,0,6,0,0,0,8,0,0,0,4,0,0,0,1,0,0,0,1,0,0,0,4,0,0,0,32,0,0,0,3,0,0,0,4,0,0,0,5,0,0,0,6,0,0,0,5,0,0,0,1,0,0,0,1,0,0,0,2,0,0,0,9,0,0,0,1,0,0,0,0,0,0,0,2,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,0,0,0,0,37,100,0,0,0,0,0,0,6,0,0,0,2,0,0,0,1,0,0,0,3,0,0,0,4,0,0,0,0,0,0,0,255,255,255,255,0,0,0,0,76,79,79,80,89,95,70,65,73,78,84,95,76,73,78,69,83,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1,0,0,0,3,0,0,0,4,0,0,0,5,0,0,0,6,0,0,0,7,0,0,0,8,0,0,0,9,0,0,0,10,0,0,0,11,0,0,0,12,0,0,0,0,0,0,0,49,50,51,52,53,54,55,56,57,48,0,0,0,0,0,0,37,100,37,99,0,0,0,0,115,116,97,116,101,45,62,103,114,105,100,95,116,121,112,101,32,61,61,32,48,0,0,0,108,111,111,112,121,46,99,0,103,97,109,101,95,116,101,120,116,95,102,111,114,109,97,116,0,0,0,0,0,0,0,0,102,45,62,111,114,100,101,114,32,61,61,32,52,0,0,0,33,34,73,108,108,101,103,97,108,32,108,105,110,101,32,115,116,97,116,101,34,0,0,0,83,0,0,0,0,0,0,0,37,100,121,0,0,0,0,0,37,100,110,0,0,0,0,0,115,116,114,108,101,110,40,114,101,116,41,32,60,61,32,40,115,105,122,101,95,116,41,108,101,110,0,0,0,0,0,0,101,110,99,111,100,101,95,115,111,108,118,101,95,109,111,118,101,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,0,0,0,0,10,0,0,0,11,0,0,0,12,0,0,0,13,0,0,0,115,115,116,97,116,101,45,62,115,111,108,118,101,114,95,115,116,97,116,117,115,32,61,61,32,83,79,76,86,69,82,95,73,78,67,79,77,80,76,69,84,69,0,0,0,0,0,0,108,111,111,112,95,100,101,100,117,99,116,105,111,110,115,0,112,114,111,103,114,101,115,115,32,61,61,32,84,82,85,69,0,0,0,0,0,0,0,0,108,105,110,101,95,110,101,119,32,33,61,32,76,73,78,69,95,85,78,75,78,79,87,78,0,0,0,0,0,0,0,0,115,111,108,118,101,114,95,115,101,116,95,108,105,110,101,0,105,32,60,32,115,115,116,97,116,101,45,62,115,116,97,116,101,45,62,103,97,109,101,95,103,114,105,100,45,62,110,117,109,95,101,100,103,101,115,0,109,101,114,103,101,95,108,105,110,101,115,0,0,0,0,0,106,32,60,32,115,115,116,97,116,101,45,62,115,116,97,116,101,45,62,103,97,109,101,95,103,114,105,100,45,62,110,117,109,95,101,100,103,101,115,0,78,32,60,61,32,77,65,88,95,70,65,67,69,95,83,73,90,69,0,0,0,0,0,0,100,108,105,110,101,95,100,101,100,117,99,116,105,111,110,115,0,0,0,0,0,0,0,0,103,45,62,101,100,103,101,115,91,101,49,93,46,100,111,116,50,32,61,61,32,103,45,62,101,100,103,101,115,91,101,50,93,46,100,111,116,49,32,124,124,32,103,45,62,101,100,103,101,115,91,101,49,93,46,100,111,116,50,32,61,61,32,103,45,62,101,100,103,101,115,91,101,50,93,46,100,111,116,50,0,0,0,0,0,0,0,0,116,114,105,118,105,97,108,95,100,101,100,117,99,116,105,111,110,115,0,0,0,0,0,0,114,0,0,0,0,0,0,0,114,32,61,61,32,84,82,85,69,0,0,0,0,0,0,0,100,111,116,95,115,101,116,97,108,108,0,0,0,0,0,0,102,97,99,101,95,115,101,116,97,108,108,0,0,0,0,0,42,100,112,0,0,0,0,0,110,101,119,95,103,97,109,101,0,0,0,0,0,0,0,0,110,32,62,32,48,0,0,0,85,110,107,110,111,119,110,32,99,104,97,114,97,99,116,101,114,32,105,110,32,100,101,115,99,114,105,112,116,105,111,110,0,0,0,0,0,0,0,0,68,101,115,99,114,105,112,116,105,111,110,32,116,111,111,32,115,104,111,114,116,32,102,111,114,32,98,111,97,114,100,32,115,105,122,101,0,0,0,0,68,101,115,99,114,105,112,116,105,111,110,32,116,111,111,32,108,111,110,103,32,102,111,114,32,98,111,97,114,100,32,115,105,122,101,0,0,0,0,0,37,115,37,99,37,115,0,0,33,118,97,108,105,100,97,116,101,95,100,101,115,99,40,112,97,114,97,109,115,44,32,114,101,116,118,97,108,41,0,0,110,101,119,95,103,97,109,101,95,100,101,115,99,0,0,0,37,99,0,0,0,0,0,0,115,115,116,97,116,101,95,110,101,119,45,62,115,111,108,118,101,114,95,115,116,97,116,117,115,32,33,61,32,83,79,76,86,69,82,95,77,73,83,84,65,75,69,0,0,0,0,0,103,97,109,101,95,104,97,115,95,117,110,105,113,117,101,95,115,111,108,110,0,0,0,0,99,49,32,33,61,32,70,65,67,69,95,71,82,69,89,0,97,100,100,95,102,117,108,108,95,99,108,117,101,115,0,0,99,50,32,33,61,32,70,65,67,69,95,71,82,69,89,0,73,108,108,101,103,97,108,32,103,114,105,100,32,116,121,112,101,0,0,0,0,0,0,0,3,0,0,0,3,0,0,0,24,14,0,0,88,14,0,0,3,0,0,0,3,0,0,0,24,14,0,0,88,14,0,0,3,0,0,0,3,0,0,0,24,14,0,0,88,14,0,0,3,0,0,0,3,0,0,0,24,14,0,0,88,14,0,0,3,0,0,0,4,0,0,0,24,14,0,0,160,14,0,0,3,0,0,0,3,0,0,0,24,14,0,0,88,14,0,0,3,0,0,0,3,0,0,0,24,14,0,0,88,14,0,0,3,0,0,0,3,0,0,0,24,14,0,0,88,14,0,0,1,0,0,0,2,0,0,0,232,14,0,0,40,15,0,0,2,0,0,0,2,0,0,0,112,15,0,0,40,15,0,0,2,0,0,0,2,0,0,0,112,15,0,0,40,15,0,0,3,0,0,0,3,0,0,0,24,14,0,0,88,14,0,0,3,0,0,0,3,0,0,0,24,14,0,0,88,14,0,0,112,97,114,97,109,115,45,62,100,105,102,102,32,60,32,68,73,70,70,95,77,65,88,0,118,97,108,105,100,97,116,101,95,112,97,114,97,109,115,0,87,105,100,116,104,32,97,110,100,32,104,101,105,103,104,116,32,102,111,114,32,116,104,105,115,32,103,114,105,100,32,116,121,112,101,32,109,117,115,116,32,98,111,116,104,32,98,101,32,97,116,32,108,101,97,115,116,32,51,0,0,0,0,0,65,116,32,108,101,97,115,116,32,111,110,101,32,111,102,32,119,105,100,116,104,32,97,110,100,32,104,101,105,103,104,116,32,102,111,114,32,116,104,105,115,32,103,114,105,100,32,116,121,112,101,32,109,117,115,116,32,98,101,32,97,116,32,108,101,97,115,116,32,51,0,0,65,116,32,108,101,97,115,116,32,111,110,101,32,111,102,32,119,105,100,116,104,32,97,110,100,32,104,101,105,103,104,116,32,102,111,114,32,116,104,105,115,32,103,114,105,100,32,116,121,112,101,32,109,117,115,116,32,98,101,32,97,116,32,108,101,97,115,116,32,52,0,0,87,105,100,116,104,32,97,110,100,32,104,101,105,103,104,116,32,102,111,114,32,116,104,105,115,32,103,114,105,100,32,116,121,112,101,32,109,117,115,116,32,98,111,116,104,32,98,101,32,97,116,32,108,101,97,115,116,32,49,0,0,0,0,0,65,116,32,108,101,97,115,116,32,111,110,101,32,111,102,32,119,105,100,116,104,32,97,110,100,32,104,101,105,103,104,116,32,102,111,114,32,116,104,105,115,32,103,114,105,100,32,116,121,112,101,32,109,117,115,116,32,98,101,32,97,116,32,108,101,97,115,116,32,50,0,0,87,105,100,116,104,32,97,110,100,32,104,101,105,103,104,116,32,102,111,114,32,116,104,105,115,32,103,114,105,100,32,116,121,112,101,32,109,117,115,116,32,98,111,116,104,32,98,101,32,97,116,32,108,101,97,115,116,32,50,0,0,0,0,0,87,105,100,116,104,0,0,0,72,101,105,103,104,116,0,0,71,114,105,100,32,116,121,112,101,0,0,0,0,0,0,0,58,83,113,117,97,114,101,115,58,84,114,105,97,110,103,117,108,97,114,58,72,111,110,101,121,99,111,109,98,58,83,110,117,98,45,83,113,117,97,114,101,58,67,97,105,114,111,58,71,114,101,97,116,45,72,101,120,97,103,111,110,97,108,58,79,99,116,97,103,111,110,97,108,58,75,105,116,101,115,58,70,108,111,114,101,116,58,68,111,100,101,99,97,103,111,110,97,108,58,71,114,101,97,116,45,68,111,100,101,99,97,103,111,110,97,108,58,80,101,110,114,111,115,101,32,40,107,105,116,101,47,100,97,114,116,41,58,80,101,110,114,111,115,101,32,40,114,104,111,109,98,115,41,0,0,0,0,0,0,0,68,105,102,102,105,99,117,108,116,121,0,0,0,0,0,0,58,69,97,115,121,58,78,111,114,109,97,108,58,84,114,105,99,107,121,58,72,97,114,100,0,0,0,0,0,0,0,0,37,100,120,37,100,116,37,100,0,0,0,0,0,0,0,0,100,37,99,0,0,0,0,0,101,110,116,104,0,0,0,0,7,0,0,0,7,0,0,0,0,0,0,0,0,0,0,0,10,0,0,0,10,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,7,0,0,0,1,0,0,0,0,0,0,0,10,0,0,0,10,0,0,0,1,0,0,0,0,0,0,0,7,0,0,0,7,0,0,0,3,0,0,0,0,0,0,0,10,0,0,0,10,0,0,0,3,0,0,0,0,0,0,0,10,0,0,0,10,0,0,0,3,0,0,0,1,0,0,0,12,0,0,0,10,0,0,0,3,0,0,0,2,0,0,0,7,0,0,0,7,0,0,0,3,0,0,0,3,0,0,0,9,0,0,0,9,0,0,0,3,0,0,0,4,0,0,0,5,0,0,0,4,0,0,0,3,0,0,0,5,0,0,0,7,0,0,0,7,0,0,0,3,0,0,0,6,0,0,0,5,0,0,0,5,0,0,0,3,0,0,0,7,0,0,0,5,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,5,0,0,0,4,0,0,0,3,0,0,0,9,0,0,0,5,0,0,0,4,0,0,0,3,0,0,0,10,0,0,0,10,0,0,0,10,0,0,0,3,0,0,0,11,0,0,0,10,0,0,0,10,0,0,0,3,0,0,0,12,0,0,0,37,100,120,37,100,32,37,115,32,45,32,37,115,0,0,0,88,18,0,0,96,18,0,0,112,18,0,0,128,18,0,0,144,18,0,0,152,18,0,0,168,18,0,0,184,18,0,0,192,18,0,0,200,18,0,0,216,18,0,0,240,18,0,0,8,19,0,0,0,0,0,0,56,18,0,0,64,18,0,0,72,18,0,0,80,18,0,0,69,97,115,121,0,0,0,0,78,111,114,109,97,108,0,0,84,114,105,99,107,121,0,0,72,97,114,100,0,0,0,0,83,113,117,97,114,101,115,0,84,114,105,97,110,103,117,108,97,114,0,0,0,0,0,0,72,111,110,101,121,99,111,109,98,0,0,0,0,0,0,0,83,110,117,98,45,83,113,117,97,114,101,0,0,0,0,0,67,97,105,114,111,0,0,0,71,114,101,97,116,45,72,101,120,97,103,111,110,97,108,0,79,99,116,97,103,111,110,97,108,0,0,0,0,0,0,0,75,105,116,101,115,0,0,0,70,108,111,114,101,116,0,0,68,111,100,101,99,97,103,111,110,97,108,0,0,0,0,0,71,114,101,97,116,45,68,111,100,101,99,97,103,111,110,97,108,0,0,0,0,0,0,0,80,101,110,114,111,115,101,32,40,107,105,116,101,47,100,97,114,116,41,0,0,0,0,0,80,101,110,114,111,115,101,32,40,114,104,111,109,98,115,41,0,0,0,0,0,0,0,0,111,117,116,32,111,102,32,109,101,109,111,114,121,0,0,0,37,115,95,84,73,76,69,83,73,90,69,0,0,0,0,0,37,100,0,0,0,0,0,0,37,115,95,68,69,70,65,85,76,84,0,0,0,0,0,0,109,101,45,62,110,115,116,97,116,101,115,32,61,61,32,48,0,0,0,0,0,0,0,0,109,105,100,101,110,100,46,99,0,0,0,0,0,0,0,0,109,105,100,101,110,100,95,110,101,119,95,103,97,109,101,0,109,111,118,101,115,116,114,32,38,38,32,33,109,115,103,0,115,0,0,0,0,0,0,0,109,101,45,62,115,116,97,116,101,112,111,115,32,62,61,32,49,0,0,0,0,0,0,0,109,105,100,101,110,100,95,114,101,115,116,97,114,116,95,103,97,109,101,0,0,0,0,0,109,101,45,62,100,114,97,119,105,110,103,0,0,0,0,0,109,105,100,101,110,100,95,114,101,100,114,97,119,0,0,0,109,101,45,62,100,105,114,32,33,61,32,48,0,0,0,0,0,0,0,0,0,0,0,0,37,115,95,67,79,76,79,85,82,95,37,100,0,0,0,0,37,50,120,37,50,120,37,50,120,0,0,0,0,0,0,0,37,115,95,80,82,69,83,69,84,83,0,0,0,0,0,0,110,32,62,61,32,48,32,38,38,32,110,32,60,32,109,101,45,62,110,112,114,101,115,101,116,115,0,0,0,0,0,0,109,105,100,101,110,100,95,102,101,116,99,104,95,112,114,101,115,101,116,0,0,0,0,0,119,105,110,116,105,116,108,101,0,0,0,0,0,0,0,0,109,105,100,101,110,100,95,103,101,116,95,99,111,110,102,105,103,0,0,0,0,0,0,0,37,115,32,99,111,110,102,105,103,117,114,97,116,105,111,110,0,0,0,0,0,0,0,0,37,115,32,37,115,32,115,101,108,101,99,116,105,111,110,0,114,97,110,100,111,109,0,0,103,97,109,101,0,0,0,0,71,97,109,101,32,114,97,110,100,111,109,32,115,101,101,100,0,0,0,0,0,0,0,0,71,97,109,101,32,73,68,0,112,97,114,115,116,114,0,0,37,115,37,99,37,115,0,0,33,34,87,101,32,115,104,111,117,108,100,110,39,116,32,98,101,32,104,101,114,101,34,0,109,105,100,101,110,100,95,103,101,116,95,103,97,109,101,95,105,100,0,0,0,0,0,0,109,101,45,62,100,101,115,99,0,0,0,0,0,0,0,0,37,115,58,37,115,0,0,0,109,105,100,101,110,100,95,103,101,116,95,114,97,110,100,111,109,95,115,101,101,100,0,0,37,115,35,37,115,0,0,0,84,104,105,115,32,103,97,109,101,32,100,111,101,115,32,110,111,116,32,115,117,112,112,111,114,116,32,116,104,101,32,83,111,108,118,101,32,111,112,101,114,97,116,105,111,110,0,0,78,111,32,103,97,109,101,32,115,101,116,32,117,112,32,116,111,32,115,111,108,118,101,0,83,111,108,118,101,32,111,112,101,114,97,116,105,111,110,32,102,97,105,108,101,100,0,0,109,105,100,101,110,100,95,115,111,108,118,101,0,0,0,0,91,37,100,58,37,48,50,100,93,32,0,0,0,0,0,0,115,32,33,61,32,78,85,76,76,0,0,0,0,0,0,0,109,105,100,101,110,100,95,114,101,97,108,108,121,95,112,114,111,99,101,115,115,95,107,101,121,0,0,0,0,0,0,0,109,111,118,101,115,116,114,32,33,61,32,78,85,76,76,0,40,97,110,103,32,37,32,51,54,41,32,61,61,32,48,0,112,101,110,114,111,115,101,46,99,0,0,0,0,0,0,0,118,95,114,111,116,97,116,101,0,0,0,0,0,0,0,0,98,105,116,115,32,60,32,51,50,0,0,0,0,0,0,0,114,97,110,100,111,109,46,99,0,0,0,0,0,0,0,0,114,97,110,100,111,109,95,117,112,116,111,0,0,0,0,0,114,101,108,97,116,105,111,110,32,61,61,32,82,69,76,50,51,52,95,76,84,32,124,124,32,114,101,108,97,116,105,111,110,32,61,61,32,82,69,76,50,51,52,95,71,84,0,0,116,114,101,101,50,51,52,46,99,0,0,0,0,0,0,0,102,105,110,100,114,101,108,112,111,115,50,51,52,0,0,0,33,108,101,102,116,45,62,101,108,101,109,115,91,50,93,32,38,38,32,33,114,105,103,104,116,45,62,101,108,101,109,115,91,50,93,0,0,0,0,0,116,114,97,110,115,50,51,52,95,115,117,98,116,114,101,101,95,109,101,114,103,101,0,0,48,0,0,0,0,0,0,0,100,101,108,112,111,115,50,51,52,95,105,110,116,101,114,110,97,108,0,0,0,0,0,0,110,45,62,101,108,101,109,115,91,107,105,93,0,0,0,0,33,110,45,62,107,105,100,115,91,48,93,0,0,0,0,0,110,32,61,61,32,116,45,62,114,111,111,116,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], "i8", ALLOC_NONE, Runtime.GLOBAL_BASE);




var tempDoublePtr = Runtime.alignMemory(allocate(12, "i8", ALLOC_STATIC), 8);

assert(tempDoublePtr % 8 == 0);

function copyTempFloat(ptr) { // functions, because inlining this code increases code size too much

  HEAP8[tempDoublePtr] = HEAP8[ptr];

  HEAP8[tempDoublePtr+1] = HEAP8[ptr+1];

  HEAP8[tempDoublePtr+2] = HEAP8[ptr+2];

  HEAP8[tempDoublePtr+3] = HEAP8[ptr+3];

}

function copyTempDouble(ptr) {

  HEAP8[tempDoublePtr] = HEAP8[ptr];

  HEAP8[tempDoublePtr+1] = HEAP8[ptr+1];

  HEAP8[tempDoublePtr+2] = HEAP8[ptr+2];

  HEAP8[tempDoublePtr+3] = HEAP8[ptr+3];

  HEAP8[tempDoublePtr+4] = HEAP8[ptr+4];

  HEAP8[tempDoublePtr+5] = HEAP8[ptr+5];

  HEAP8[tempDoublePtr+6] = HEAP8[ptr+6];

  HEAP8[tempDoublePtr+7] = HEAP8[ptr+7];

}






  Module["_strlen"] = _strlen;

  function __reallyNegative(x) {
      return x < 0 || (x === 0 && (1/x) === -Infinity);
    }function __formatString(format, varargs) {
      var textIndex = format;
      var argIndex = 0;
      function getNextArg(type) {
        // NOTE: Explicitly ignoring type safety. Otherwise this fails:
        //       int x = 4; printf("%c\n", (char)x);
        var ret;
        if (type === 'double') {
          ret = (HEAP32[((tempDoublePtr)>>2)]=HEAP32[(((varargs)+(argIndex))>>2)],HEAP32[(((tempDoublePtr)+(4))>>2)]=HEAP32[(((varargs)+((argIndex)+(4)))>>2)],(+(HEAPF64[(tempDoublePtr)>>3])));
        } else if (type == 'i64') {
          ret = [HEAP32[(((varargs)+(argIndex))>>2)],
                 HEAP32[(((varargs)+(argIndex+4))>>2)]];

        } else {
          type = 'i32'; // varargs are always i32, i64, or double
          ret = HEAP32[(((varargs)+(argIndex))>>2)];
        }
        argIndex += Runtime.getNativeFieldSize(type);
        return ret;
      }

      var ret = [];
      var curr, next, currArg;
      while(1) {
        var startTextIndex = textIndex;
        curr = HEAP8[(textIndex)];
        if (curr === 0) break;
        next = HEAP8[((textIndex+1)|0)];
        if (curr == 37) {
          // Handle flags.
          var flagAlwaysSigned = false;
          var flagLeftAlign = false;
          var flagAlternative = false;
          var flagZeroPad = false;
          var flagPadSign = false;
          flagsLoop: while (1) {
            switch (next) {
              case 43:
                flagAlwaysSigned = true;
                break;
              case 45:
                flagLeftAlign = true;
                break;
              case 35:
                flagAlternative = true;
                break;
              case 48:
                if (flagZeroPad) {
                  break flagsLoop;
                } else {
                  flagZeroPad = true;
                  break;
                }
              case 32:
                flagPadSign = true;
                break;
              default:
                break flagsLoop;
            }
            textIndex++;
            next = HEAP8[((textIndex+1)|0)];
          }

          // Handle width.
          var width = 0;
          if (next == 42) {
            width = getNextArg('i32');
            textIndex++;
            next = HEAP8[((textIndex+1)|0)];
          } else {
            while (next >= 48 && next <= 57) {
              width = width * 10 + (next - 48);
              textIndex++;
              next = HEAP8[((textIndex+1)|0)];
            }
          }

          // Handle precision.
          var precisionSet = false, precision = -1;
          if (next == 46) {
            precision = 0;
            precisionSet = true;
            textIndex++;
            next = HEAP8[((textIndex+1)|0)];
            if (next == 42) {
              precision = getNextArg('i32');
              textIndex++;
            } else {
              while(1) {
                var precisionChr = HEAP8[((textIndex+1)|0)];
                if (precisionChr < 48 ||
                    precisionChr > 57) break;
                precision = precision * 10 + (precisionChr - 48);
                textIndex++;
              }
            }
            next = HEAP8[((textIndex+1)|0)];
          }
          if (precision < 0) {
            precision = 6; // Standard default.
            precisionSet = false;
          }

          // Handle integer sizes. WARNING: These assume a 32-bit architecture!
          var argSize;
          switch (String.fromCharCode(next)) {
            case 'h':
              var nextNext = HEAP8[((textIndex+2)|0)];
              if (nextNext == 104) {
                textIndex++;
                argSize = 1; // char (actually i32 in varargs)
              } else {
                argSize = 2; // short (actually i32 in varargs)
              }
              break;
            case 'l':
              var nextNext = HEAP8[((textIndex+2)|0)];
              if (nextNext == 108) {
                textIndex++;
                argSize = 8; // long long
              } else {
                argSize = 4; // long
              }
              break;
            case 'L': // long long
            case 'q': // int64_t
            case 'j': // intmax_t
              argSize = 8;
              break;
            case 'z': // size_t
            case 't': // ptrdiff_t
            case 'I': // signed ptrdiff_t or unsigned size_t
              argSize = 4;
              break;
            default:
              argSize = null;
          }
          if (argSize) textIndex++;
          next = HEAP8[((textIndex+1)|0)];

          // Handle type specifier.
          switch (String.fromCharCode(next)) {
            case 'd': case 'i': case 'u': case 'o': case 'x': case 'X': case 'p': {
              // Integer.
              var signed = next == 100 || next == 105;
              argSize = argSize || 4;
              var currArg = getNextArg('i' + (argSize * 8));
              var origArg = currArg;
              var argText;
              // Flatten i64-1 [low, high] into a (slightly rounded) double
              if (argSize == 8) {
                currArg = Runtime.makeBigInt(currArg[0], currArg[1], next == 117);
              }
              // Truncate to requested size.
              if (argSize <= 4) {
                var limit = Math.pow(256, argSize) - 1;
                currArg = (signed ? reSign : unSign)(currArg & limit, argSize * 8);
              }
              // Format the number.
              var currAbsArg = Math.abs(currArg);
              var prefix = '';
              if (next == 100 || next == 105) {
                if (argSize == 8 && i64Math) argText = i64Math.stringify(origArg[0], origArg[1], null); else
                argText = reSign(currArg, 8 * argSize, 1).toString(10);
              } else if (next == 117) {
                if (argSize == 8 && i64Math) argText = i64Math.stringify(origArg[0], origArg[1], true); else
                argText = unSign(currArg, 8 * argSize, 1).toString(10);
                currArg = Math.abs(currArg);
              } else if (next == 111) {
                argText = (flagAlternative ? '0' : '') + currAbsArg.toString(8);
              } else if (next == 120 || next == 88) {
                prefix = (flagAlternative && currArg != 0) ? '0x' : '';
                if (argSize == 8 && i64Math) {
                  if (origArg[1]) {
                    argText = (origArg[1]>>>0).toString(16);
                    var lower = (origArg[0]>>>0).toString(16);
                    while (lower.length < 8) lower = '0' + lower;
                    argText += lower;
                  } else {
                    argText = (origArg[0]>>>0).toString(16);
                  }
                } else
                if (currArg < 0) {
                  // Represent negative numbers in hex as 2's complement.
                  currArg = -currArg;
                  argText = (currAbsArg - 1).toString(16);
                  var buffer = [];
                  for (var i = 0; i < argText.length; i++) {
                    buffer.push((0xF - parseInt(argText[i], 16)).toString(16));
                  }
                  argText = buffer.join('');
                  while (argText.length < argSize * 2) argText = 'f' + argText;
                } else {
                  argText = currAbsArg.toString(16);
                }
                if (next == 88) {
                  prefix = prefix.toUpperCase();
                  argText = argText.toUpperCase();
                }
              } else if (next == 112) {
                if (currAbsArg === 0) {
                  argText = '(nil)';
                } else {
                  prefix = '0x';
                  argText = currAbsArg.toString(16);
                }
              }
              if (precisionSet) {
                while (argText.length < precision) {
                  argText = '0' + argText;
                }
              }

              // Add sign if needed
              if (currArg >= 0) {
                if (flagAlwaysSigned) {
                  prefix = '+' + prefix;
                } else if (flagPadSign) {
                  prefix = ' ' + prefix;
                }
              }

              // Move sign to prefix so we zero-pad after the sign
              if (argText.charAt(0) == '-') {
                prefix = '-' + prefix;
                argText = argText.substr(1);
              }

              // Add padding.
              while (prefix.length + argText.length < width) {
                if (flagLeftAlign) {
                  argText += ' ';
                } else {
                  if (flagZeroPad) {
                    argText = '0' + argText;
                  } else {
                    prefix = ' ' + prefix;
                  }
                }
              }

              // Insert the result into the buffer.
              argText = prefix + argText;
              argText.split('').forEach(function(chr) {
                ret.push(chr.charCodeAt(0));
              });
              break;
            }
            case 'f': case 'F': case 'e': case 'E': case 'g': case 'G': {
              // Float.
              var currArg = getNextArg('double');
              var argText;
              if (isNaN(currArg)) {
                argText = 'nan';
                flagZeroPad = false;
              } else if (!isFinite(currArg)) {
                argText = (currArg < 0 ? '-' : '') + 'inf';
                flagZeroPad = false;
              } else {
                var isGeneral = false;
                var effectivePrecision = Math.min(precision, 20);

                // Convert g/G to f/F or e/E, as per:
                // http://pubs.opengroup.org/onlinepubs/9699919799/functions/printf.html
                if (next == 103 || next == 71) {
                  isGeneral = true;
                  precision = precision || 1;
                  var exponent = parseInt(currArg.toExponential(effectivePrecision).split('e')[1], 10);
                  if (precision > exponent && exponent >= -4) {
                    next = ((next == 103) ? 'f' : 'F').charCodeAt(0);
                    precision -= exponent + 1;
                  } else {
                    next = ((next == 103) ? 'e' : 'E').charCodeAt(0);
                    precision--;
                  }
                  effectivePrecision = Math.min(precision, 20);
                }

                if (next == 101 || next == 69) {
                  argText = currArg.toExponential(effectivePrecision);
                  // Make sure the exponent has at least 2 digits.
                  if (/[eE][-+]\d$/.test(argText)) {
                    argText = argText.slice(0, -1) + '0' + argText.slice(-1);
                  }
                } else if (next == 102 || next == 70) {
                  argText = currArg.toFixed(effectivePrecision);
                  if (currArg === 0 && __reallyNegative(currArg)) {
                    argText = '-' + argText;
                  }
                }

                var parts = argText.split('e');
                if (isGeneral && !flagAlternative) {
                  // Discard trailing zeros and periods.
                  while (parts[0].length > 1 && parts[0].indexOf('.') != -1 &&
                         (parts[0].slice(-1) == '0' || parts[0].slice(-1) == '.')) {
                    parts[0] = parts[0].slice(0, -1);
                  }
                } else {
                  // Make sure we have a period in alternative mode.
                  if (flagAlternative && argText.indexOf('.') == -1) parts[0] += '.';
                  // Zero pad until required precision.
                  while (precision > effectivePrecision++) parts[0] += '0';
                }
                argText = parts[0] + (parts.length > 1 ? 'e' + parts[1] : '');

                // Capitalize 'E' if needed.
                if (next == 69) argText = argText.toUpperCase();

                // Add sign.
                if (currArg >= 0) {
                  if (flagAlwaysSigned) {
                    argText = '+' + argText;
                  } else if (flagPadSign) {
                    argText = ' ' + argText;
                  }
                }
              }

              // Add padding.
              while (argText.length < width) {
                if (flagLeftAlign) {
                  argText += ' ';
                } else {
                  if (flagZeroPad && (argText[0] == '-' || argText[0] == '+')) {
                    argText = argText[0] + '0' + argText.slice(1);
                  } else {
                    argText = (flagZeroPad ? '0' : ' ') + argText;
                  }
                }
              }

              // Adjust case.
              if (next < 97) argText = argText.toUpperCase();

              // Insert the result into the buffer.
              argText.split('').forEach(function(chr) {
                ret.push(chr.charCodeAt(0));
              });
              break;
            }
            case 's': {
              // String.
              var arg = getNextArg('i8*');
              var argLength = arg ? _strlen(arg) : '(null)'.length;
              if (precisionSet) argLength = Math.min(argLength, precision);
              if (!flagLeftAlign) {
                while (argLength < width--) {
                  ret.push(32);
                }
              }
              if (arg) {
                for (var i = 0; i < argLength; i++) {
                  ret.push(HEAPU8[((arg++)|0)]);
                }
              } else {
                ret = ret.concat(intArrayFromString('(null)'.substr(0, argLength), true));
              }
              if (flagLeftAlign) {
                while (argLength < width--) {
                  ret.push(32);
                }
              }
              break;
            }
            case 'c': {
              // Character.
              if (flagLeftAlign) ret.push(getNextArg('i8'));
              while (--width > 0) {
                ret.push(32);
              }
              if (!flagLeftAlign) ret.push(getNextArg('i8'));
              break;
            }
            case 'n': {
              // Write the length written so far to the next parameter.
              var ptr = getNextArg('i32*');
              HEAP32[((ptr)>>2)]=ret.length;
              break;
            }
            case '%': {
              // Literal percent sign.
              ret.push(curr);
              break;
            }
            default: {
              // Unknown specifiers remain untouched.
              for (var i = startTextIndex; i < textIndex + 2; i++) {
                ret.push(HEAP8[(i)]);
              }
            }
          }
          textIndex += 2;
          // TODO: Support a/A (hex float) and m (last error) specifiers.
          // TODO: Support %1${specifier} for arg selection.
        } else {
          ret.push(curr);
          textIndex += 1;
        }
      }
      return ret;
    }

  function _malloc(bytes) {
      /* Over-allocate to make sure it is byte-aligned by 8.
       * This will leak memory, but this is only the dummy
       * implementation (replaced by dlmalloc normally) so
       * not an issue.
       */
      var ptr = Runtime.dynamicAlloc(bytes + 8);
      return (ptr+8) & 0xFFFFFFF8;
    }
  Module["_malloc"] = _malloc;function _snprintf(s, n, format, varargs) {
      // int snprintf(char *restrict s, size_t n, const char *restrict format, ...);
      // http://pubs.opengroup.org/onlinepubs/000095399/functions/printf.html
      var result = __formatString(format, varargs);
      var limit = (n === undefined) ? result.length
                                    : Math.min(result.length, Math.max(n - 1, 0));
      if (s < 0) {
        s = -s;
        var buf = _malloc(limit+1);
        HEAP32[((s)>>2)]=buf;
        s = buf;
      }
      for (var i = 0; i < limit; i++) {
        HEAP8[(((s)+(i))|0)]=result[i];
      }
      if (limit < n || (n === undefined)) HEAP8[(((s)+(i))|0)]=0;
      return result.length;
    }function _vsnprintf(s, n, format, va_arg) {
      return _snprintf(s, n, format, HEAP32[((va_arg)>>2)]);
    }



  function __getFloat(text) {
      return /^[+-]?[0-9]*\.?[0-9]+([eE][+-]?[0-9]+)?/.exec(text);
    }function __scanString(format, get, unget, varargs) {
      if (!__scanString.whiteSpace) {
        __scanString.whiteSpace = {};
        __scanString.whiteSpace[32] = 1;
        __scanString.whiteSpace[9] = 1;
        __scanString.whiteSpace[10] = 1;
        __scanString.whiteSpace[11] = 1;
        __scanString.whiteSpace[12] = 1;
        __scanString.whiteSpace[13] = 1;
      }
      // Supports %x, %4x, %d.%d, %lld, %s, %f, %lf.
      // TODO: Support all format specifiers.
      format = Pointer_stringify(format);
      var soFar = 0;
      if (format.indexOf('%n') >= 0) {
        // need to track soFar
        var _get = get;
        get = function get() {
          soFar++;
          return _get();
        }
        var _unget = unget;
        unget = function unget() {
          soFar--;
          return _unget();
        }
      }
      var formatIndex = 0;
      var argsi = 0;
      var fields = 0;
      var argIndex = 0;
      var next;

      mainLoop:
      for (var formatIndex = 0; formatIndex < format.length;) {
        if (format[formatIndex] === '%' && format[formatIndex+1] == 'n') {
          var argPtr = HEAP32[(((varargs)+(argIndex))>>2)];
          argIndex += Runtime.getAlignSize('void*', null, true);
          HEAP32[((argPtr)>>2)]=soFar;
          formatIndex += 2;
          continue;
        }

        if (format[formatIndex] === '%') {
          var nextC = format.indexOf('c', formatIndex+1);
          if (nextC > 0) {
            var maxx = 1;
            if (nextC > formatIndex+1) {
              var sub = format.substring(formatIndex+1, nextC);
              maxx = parseInt(sub);
              if (maxx != sub) maxx = 0;
            }
            if (maxx) {
              var argPtr = HEAP32[(((varargs)+(argIndex))>>2)];
              argIndex += Runtime.getAlignSize('void*', null, true);
              fields++;
              for (var i = 0; i < maxx; i++) {
                next = get();
                HEAP8[((argPtr++)|0)]=next;
                if (next === 0) return i > 0 ? fields : fields-1; // we failed to read the full length of this field
              }
              formatIndex += nextC - formatIndex + 1;
              continue;
            }
          }
        }

        // handle %[...]
        if (format[formatIndex] === '%' && format.indexOf('[', formatIndex+1) > 0) {
          var match = /\%([0-9]*)\[(\^)?(\]?[^\]]*)\]/.exec(format.substring(formatIndex));
          if (match) {
            var maxNumCharacters = parseInt(match[1]) || Infinity;
            var negateScanList = (match[2] === '^');
            var scanList = match[3];

            // expand "middle" dashs into character sets
            var middleDashMatch;
            while ((middleDashMatch = /([^\-])\-([^\-])/.exec(scanList))) {
              var rangeStartCharCode = middleDashMatch[1].charCodeAt(0);
              var rangeEndCharCode = middleDashMatch[2].charCodeAt(0);
              for (var expanded = ''; rangeStartCharCode <= rangeEndCharCode; expanded += String.fromCharCode(rangeStartCharCode++));
              scanList = scanList.replace(middleDashMatch[1] + '-' + middleDashMatch[2], expanded);
            }

            var argPtr = HEAP32[(((varargs)+(argIndex))>>2)];
            argIndex += Runtime.getAlignSize('void*', null, true);
            fields++;

            for (var i = 0; i < maxNumCharacters; i++) {
              next = get();
              if (negateScanList) {
                if (scanList.indexOf(String.fromCharCode(next)) < 0) {
                  HEAP8[((argPtr++)|0)]=next;
                } else {
                  unget();
                  break;
                }
              } else {
                if (scanList.indexOf(String.fromCharCode(next)) >= 0) {
                  HEAP8[((argPtr++)|0)]=next;
                } else {
                  unget();
                  break;
                }
              }
            }

            // write out null-terminating character
            HEAP8[((argPtr++)|0)]=0;
            formatIndex += match[0].length;

            continue;
          }
        }
        // remove whitespace
        while (1) {
          next = get();
          if (next == 0) return fields;
          if (!(next in __scanString.whiteSpace)) break;
        }
        unget();

        if (format[formatIndex] === '%') {
          formatIndex++;
          var suppressAssignment = false;
          if (format[formatIndex] == '*') {
            suppressAssignment = true;
            formatIndex++;
          }
          var maxSpecifierStart = formatIndex;
          while (format[formatIndex].charCodeAt(0) >= 48 &&
                 format[formatIndex].charCodeAt(0) <= 57) {
            formatIndex++;
          }
          var max_;
          if (formatIndex != maxSpecifierStart) {
            max_ = parseInt(format.slice(maxSpecifierStart, formatIndex), 10);
          }
          var long_ = false;
          var half = false;
          var longLong = false;
          if (format[formatIndex] == 'l') {
            long_ = true;
            formatIndex++;
            if (format[formatIndex] == 'l') {
              longLong = true;
              formatIndex++;
            }
          } else if (format[formatIndex] == 'h') {
            half = true;
            formatIndex++;
          }
          var type = format[formatIndex];
          formatIndex++;
          var curr = 0;
          var buffer = [];
          // Read characters according to the format. floats are trickier, they may be in an unfloat state in the middle, then be a valid float later
          if (type == 'f' || type == 'e' || type == 'g' ||
              type == 'F' || type == 'E' || type == 'G') {
            next = get();
            while (next > 0 && (!(next in __scanString.whiteSpace)))  {
              buffer.push(String.fromCharCode(next));
              next = get();
            }
            var m = __getFloat(buffer.join(''));
            var last = m ? m[0].length : 0;
            for (var i = 0; i < buffer.length - last + 1; i++) {
              unget();
            }
            buffer.length = last;
          } else {
            next = get();
            var first = true;

            // Strip the optional 0x prefix for %x.
            if ((type == 'x' || type == 'X') && (next == 48)) {
              var peek = get();
              if (peek == 120 || peek == 88) {
                next = get();
              } else {
                unget();
              }
            }

            while ((curr < max_ || isNaN(max_)) && next > 0) {
              if (!(next in __scanString.whiteSpace) && // stop on whitespace
                  (type == 's' ||
                   ((type === 'd' || type == 'u' || type == 'i') && ((next >= 48 && next <= 57) ||
                                                                     (first && next == 45))) ||
                   ((type === 'x' || type === 'X') && (next >= 48 && next <= 57 ||
                                     next >= 97 && next <= 102 ||
                                     next >= 65 && next <= 70))) &&
                  (formatIndex >= format.length || next !== format[formatIndex].charCodeAt(0))) { // Stop when we read something that is coming up
                buffer.push(String.fromCharCode(next));
                next = get();
                curr++;
                first = false;
              } else {
                break;
              }
            }
            unget();
          }
          if (buffer.length === 0) return 0;  // Failure.
          if (suppressAssignment) continue;

          var text = buffer.join('');
          var argPtr = HEAP32[(((varargs)+(argIndex))>>2)];
          argIndex += Runtime.getAlignSize('void*', null, true);
          switch (type) {
            case 'd': case 'u': case 'i':
              if (half) {
                HEAP16[((argPtr)>>1)]=parseInt(text, 10);
              } else if (longLong) {
                (tempI64 = [parseInt(text, 10)>>>0,(tempDouble=parseInt(text, 10),(+(Math_abs(tempDouble))) >= (+1) ? (tempDouble > (+0) ? ((Math_min((+(Math_floor((tempDouble)/(+4294967296)))), (+4294967295)))|0)>>>0 : (~~((+(Math_ceil((tempDouble - +(((~~(tempDouble)))>>>0))/(+4294967296))))))>>>0) : 0)],HEAP32[((argPtr)>>2)]=tempI64[0],HEAP32[(((argPtr)+(4))>>2)]=tempI64[1]);
              } else {
                HEAP32[((argPtr)>>2)]=parseInt(text, 10);
              }
              break;
            case 'X':
            case 'x':
              HEAP32[((argPtr)>>2)]=parseInt(text, 16);
              break;
            case 'F':
            case 'f':
            case 'E':
            case 'e':
            case 'G':
            case 'g':
            case 'E':
              // fallthrough intended
              if (long_) {
                HEAPF64[((argPtr)>>3)]=parseFloat(text);
              } else {
                HEAPF32[((argPtr)>>2)]=parseFloat(text);
              }
              break;
            case 's':
              var array = intArrayFromString(text);
              for (var j = 0; j < array.length; j++) {
                HEAP8[(((argPtr)+(j))|0)]=array[j];
              }
              break;
          }
          fields++;
        } else if (format[formatIndex].charCodeAt(0) in __scanString.whiteSpace) {
          next = get();
          while (next in __scanString.whiteSpace) {
            if (next <= 0) break mainLoop;  // End of input.
            next = get();
          }
          unget(next);
          formatIndex++;
        } else {
          // Not a specifier.
          next = get();
          if (format[formatIndex].charCodeAt(0) !== next) {
            unget(next);
            break mainLoop;
          }
          formatIndex++;
        }
      }
      return fields;
    }function _sscanf(s, format, varargs) {
      // int sscanf(const char *restrict s, const char *restrict format, ... );
      // http://pubs.opengroup.org/onlinepubs/000095399/functions/scanf.html
      var index = 0;
      function get() { return HEAP8[(((s)+(index++))|0)]; };
      function unget() { index--; };
      return __scanString(format, get, unget, varargs);
    }

  function ___assert_fail(condition, filename, line, func) {
      ABORT = true;
      throw 'Assertion failed: ' + Pointer_stringify(condition) + ', at: ' + [filename ? Pointer_stringify(filename) : 'unknown filename', line, func ? Pointer_stringify(func) : 'unknown function'] + ' at ' + stackTrace();
    }


  Module["_memset"] = _memset;


  Module["_strcat"] = _strcat;

  function _js_canvas_draw_update(x, y, w, h) {
          /*
           * Currently we do this in a really simple way, just by taking
           * the smallest rectangle containing all updates so far. We
           * could instead keep the data in a richer form (e.g. retain
           * multiple smaller rectangles needing update, and only redraw
           * the whole thing beyond a certain threshold) but this will
           * do for now.
           */
          if (update_xmin === undefined || update_xmin > x) update_xmin = x;
          if (update_ymin === undefined || update_ymin > y) update_ymin = y;
          if (update_xmax === undefined || update_xmax < x+w) update_xmax = x+w;
          if (update_ymax === undefined || update_ymax < y+h) update_ymax = y+h;
      }

  function _abort() {
      Module['abort']();
    }

  function _toupper(chr) {
      if (chr >= 97 && chr <= 122) {
        return chr - 97 + 65;
      } else {
        return chr;
      }
    }

  function _js_canvas_draw_circle(x, y, r, fill, outline) {
          ctx.beginPath();
          ctx.arc(x + 0.5, y + 0.5, r, 0, 2*Math.PI);
          if (fill != 0) {
              ctx.fillStyle = Pointer_stringify(fill);
              ctx.fill();
          }
          ctx.lineWidth = '1';
          ctx.lineCap = 'round';
          ctx.lineJoin = 'round';
          ctx.strokeStyle = Pointer_stringify(outline);
          ctx.stroke();
      }

  function _isdigit(chr) {
      return chr >= 48 && chr <= 57;
    }

  function _js_update_permalinks(desc, seed) {
          desc = Pointer_stringify(desc);
          permalink_desc.href = "#" + desc;

          if (seed == 0) {
              permalink_seed.style.display = "none";
          } else {
              seed = Pointer_stringify(seed);
              permalink_seed.href = "#" + seed;
              permalink_seed.style.display = "inline";
          }
      }

  function _js_get_date_64(ptr) {
          var d = (new Date()).valueOf();
          setValue(ptr, d, 'i64');
      }


  function _js_canvas_end_draw() {
          if (update_xmin !== undefined) {
              var onscreen_ctx = onscreen_canvas.getContext('2d');
              onscreen_ctx.drawImage(offscreen_canvas,
                                     update_xmin, update_ymin,
                                     update_xmax - update_xmin,
                                     update_ymax - update_ymin,
                                     update_xmin, update_ymin,
                                     update_xmax - update_xmin,
                                     update_ymax - update_ymin);
          }
          ctx = null;
      }

  function _js_deactivate_timer() {
          if (timer !== null) {
              clearInterval(timer);
              timer = null;
          }
      }

  function _js_canvas_start_draw() {
          ctx = offscreen_canvas.getContext('2d');
          update_xmin = update_xmax = update_ymin = update_ymax = undefined;
      }

  var _fabs=Math_abs;

  var _floor=Math_floor;

  function _js_focus_canvas() {
          onscreen_canvas.focus();
      }

  function _js_canvas_copy_from_blitter(id, x, y, w, h) {
          ctx.drawImage(blitters[id],
                        0, 0, w, h,
                        x, y, w, h);
      }

  function _js_canvas_new_blitter(w, h) {
          var id = blittercount++;
          blitters[id] = document.createElement("canvas");
          blitters[id].width = w;
          blitters[id].height = h;
          return id;
      }

  var _sqrt=Math_sqrt;


  function _emscripten_memcpy_big(dest, src, num) {
      HEAPU8.set(HEAPU8.subarray(src, src+num), dest);
      return dest;
    }
  Module["_memcpy"] = _memcpy;

  function _js_dialog_cleanup() {
          document.body.removeChild(dlg_dimmer);
          document.body.removeChild(dlg_form);
          dlg_dimmer = dlg_form = null;
          onscreen_canvas.focus();
      }

  var _abs=Math_abs;




  var ERRNO_CODES={EPERM:1,ENOENT:2,ESRCH:3,EINTR:4,EIO:5,ENXIO:6,E2BIG:7,ENOEXEC:8,EBADF:9,ECHILD:10,EAGAIN:11,EWOULDBLOCK:11,ENOMEM:12,EACCES:13,EFAULT:14,ENOTBLK:15,EBUSY:16,EEXIST:17,EXDEV:18,ENODEV:19,ENOTDIR:20,EISDIR:21,EINVAL:22,ENFILE:23,EMFILE:24,ENOTTY:25,ETXTBSY:26,EFBIG:27,ENOSPC:28,ESPIPE:29,EROFS:30,EMLINK:31,EPIPE:32,EDOM:33,ERANGE:34,ENOMSG:42,EIDRM:43,ECHRNG:44,EL2NSYNC:45,EL3HLT:46,EL3RST:47,ELNRNG:48,EUNATCH:49,ENOCSI:50,EL2HLT:51,EDEADLK:35,ENOLCK:37,EBADE:52,EBADR:53,EXFULL:54,ENOANO:55,EBADRQC:56,EBADSLT:57,EDEADLOCK:35,EBFONT:59,ENOSTR:60,ENODATA:61,ETIME:62,ENOSR:63,ENONET:64,ENOPKG:65,EREMOTE:66,ENOLINK:67,EADV:68,ESRMNT:69,ECOMM:70,EPROTO:71,EMULTIHOP:72,EDOTDOT:73,EBADMSG:74,ENOTUNIQ:76,EBADFD:77,EREMCHG:78,ELIBACC:79,ELIBBAD:80,ELIBSCN:81,ELIBMAX:82,ELIBEXEC:83,ENOSYS:38,ENOTEMPTY:39,ENAMETOOLONG:36,ELOOP:40,EOPNOTSUPP:95,EPFNOSUPPORT:96,ECONNRESET:104,ENOBUFS:105,EAFNOSUPPORT:97,EPROTOTYPE:91,ENOTSOCK:88,ENOPROTOOPT:92,ESHUTDOWN:108,ECONNREFUSED:111,EADDRINUSE:98,ECONNABORTED:103,ENETUNREACH:101,ENETDOWN:100,ETIMEDOUT:110,EHOSTDOWN:112,EHOSTUNREACH:113,EINPROGRESS:115,EALREADY:114,EDESTADDRREQ:89,EMSGSIZE:90,EPROTONOSUPPORT:93,ESOCKTNOSUPPORT:94,EADDRNOTAVAIL:99,ENETRESET:102,EISCONN:106,ENOTCONN:107,ETOOMANYREFS:109,EUSERS:87,EDQUOT:122,ESTALE:116,ENOTSUP:95,ENOMEDIUM:123,EILSEQ:84,EOVERFLOW:75,ECANCELED:125,ENOTRECOVERABLE:131,EOWNERDEAD:130,ESTRPIPE:86};

  var ERRNO_MESSAGES={0:"Success",1:"Not super-user",2:"No such file or directory",3:"No such process",4:"Interrupted system call",5:"I/O error",6:"No such device or address",7:"Arg list too long",8:"Exec format error",9:"Bad file number",10:"No children",11:"No more processes",12:"Not enough core",13:"Permission denied",14:"Bad address",15:"Block device required",16:"Mount device busy",17:"File exists",18:"Cross-device link",19:"No such device",20:"Not a directory",21:"Is a directory",22:"Invalid argument",23:"Too many open files in system",24:"Too many open files",25:"Not a typewriter",26:"Text file busy",27:"File too large",28:"No space left on device",29:"Illegal seek",30:"Read only file system",31:"Too many links",32:"Broken pipe",33:"Math arg out of domain of func",34:"Math result not representable",35:"File locking deadlock error",36:"File or path name too long",37:"No record locks available",38:"Function not implemented",39:"Directory not empty",40:"Too many symbolic links",42:"No message of desired type",43:"Identifier removed",44:"Channel number out of range",45:"Level 2 not synchronized",46:"Level 3 halted",47:"Level 3 reset",48:"Link number out of range",49:"Protocol driver not attached",50:"No CSI structure available",51:"Level 2 halted",52:"Invalid exchange",53:"Invalid request descriptor",54:"Exchange full",55:"No anode",56:"Invalid request code",57:"Invalid slot",59:"Bad font file fmt",60:"Device not a stream",61:"No data (for no delay io)",62:"Timer expired",63:"Out of streams resources",64:"Machine is not on the network",65:"Package not installed",66:"The object is remote",67:"The link has been severed",68:"Advertise error",69:"Srmount error",70:"Communication error on send",71:"Protocol error",72:"Multihop attempted",73:"Cross mount point (not really error)",74:"Trying to read unreadable message",75:"Value too large for defined data type",76:"Given log. name not unique",77:"f.d. invalid for this operation",78:"Remote address changed",79:"Can   access a needed shared lib",80:"Accessing a corrupted shared lib",81:".lib section in a.out corrupted",82:"Attempting to link in too many libs",83:"Attempting to exec a shared library",84:"Illegal byte sequence",86:"Streams pipe error",87:"Too many users",88:"Socket operation on non-socket",89:"Destination address required",90:"Message too long",91:"Protocol wrong type for socket",92:"Protocol not available",93:"Unknown protocol",94:"Socket type not supported",95:"Not supported",96:"Protocol family not supported",97:"Address family not supported by protocol family",98:"Address already in use",99:"Address not available",100:"Network interface is not configured",101:"Network is unreachable",102:"Connection reset by network",103:"Connection aborted",104:"Connection reset by peer",105:"No buffer space available",106:"Socket is already connected",107:"Socket is not connected",108:"Can't send after socket shutdown",109:"Too many references",110:"Connection timed out",111:"Connection refused",112:"Host is down",113:"Host is unreachable",114:"Socket already connected",115:"Connection already in progress",116:"Stale file handle",122:"Quota exceeded",123:"No medium (in tape drive)",125:"Operation canceled",130:"Previous owner died",131:"State not recoverable"};


  var ___errno_state=0;function ___setErrNo(value) {
      // For convenient setting and returning of errno.
      HEAP32[((___errno_state)>>2)]=value;
      return value;
    }

  var TTY={ttys:[],init:function () {
        // https://github.com/kripken/emscripten/pull/1555
        // if (ENVIRONMENT_IS_NODE) {
        //   // currently, FS.init does not distinguish if process.stdin is a file or TTY
        //   // device, it always assumes it's a TTY device. because of this, we're forcing
        //   // process.stdin to UTF8 encoding to at least make stdin reading compatible
        //   // with text files until FS.init can be refactored.
        //   process['stdin']['setEncoding']('utf8');
        // }
      },shutdown:function () {
        // https://github.com/kripken/emscripten/pull/1555
        // if (ENVIRONMENT_IS_NODE) {
        //   // inolen: any idea as to why node -e 'process.stdin.read()' wouldn't exit immediately (with process.stdin being a tty)?
        //   // isaacs: because now it's reading from the stream, you've expressed interest in it, so that read() kicks off a _read() which creates a ReadReq operation
        //   // inolen: I thought read() in that case was a synchronous operation that just grabbed some amount of buffered data if it exists?
        //   // isaacs: it is. but it also triggers a _read() call, which calls readStart() on the handle
        //   // isaacs: do process.stdin.pause() and i'd think it'd probably close the pending call
        //   process['stdin']['pause']();
        // }
      },register:function (dev, ops) {
        TTY.ttys[dev] = { input: [], output: [], ops: ops };
        FS.registerDevice(dev, TTY.stream_ops);
      },stream_ops:{open:function (stream) {
          var tty = TTY.ttys[stream.node.rdev];
          if (!tty) {
            throw new FS.ErrnoError(ERRNO_CODES.ENODEV);
          }
          stream.tty = tty;
          stream.seekable = false;
        },close:function (stream) {
          // flush any pending line data
          if (stream.tty.output.length) {
            stream.tty.ops.put_char(stream.tty, 10);
          }
        },read:function (stream, buffer, offset, length, pos /* ignored */) {
          if (!stream.tty || !stream.tty.ops.get_char) {
            throw new FS.ErrnoError(ERRNO_CODES.ENXIO);
          }
          var bytesRead = 0;
          for (var i = 0; i < length; i++) {
            var result;
            try {
              result = stream.tty.ops.get_char(stream.tty);
            } catch (e) {
              throw new FS.ErrnoError(ERRNO_CODES.EIO);
            }
            if (result === undefined && bytesRead === 0) {
              throw new FS.ErrnoError(ERRNO_CODES.EAGAIN);
            }
            if (result === null || result === undefined) break;
            bytesRead++;
            buffer[offset+i] = result;
          }
          if (bytesRead) {
            stream.node.timestamp = Date.now();
          }
          return bytesRead;
        },write:function (stream, buffer, offset, length, pos) {
          if (!stream.tty || !stream.tty.ops.put_char) {
            throw new FS.ErrnoError(ERRNO_CODES.ENXIO);
          }
          for (var i = 0; i < length; i++) {
            try {
              stream.tty.ops.put_char(stream.tty, buffer[offset+i]);
            } catch (e) {
              throw new FS.ErrnoError(ERRNO_CODES.EIO);
            }
          }
          if (length) {
            stream.node.timestamp = Date.now();
          }
          return i;
        }},default_tty_ops:{get_char:function (tty) {
          if (!tty.input.length) {
            var result = null;
            if (ENVIRONMENT_IS_NODE) {
              result = process['stdin']['read']();
              if (!result) {
                if (process['stdin']['_readableState'] && process['stdin']['_readableState']['ended']) {
                  return null;  // EOF
                }
                return undefined;  // no data available
              }
            } else if (typeof window != 'undefined' &&
              typeof window.prompt == 'function') {
              // Browser.
              result = window.prompt('Input: ');  // returns null on cancel
              if (result !== null) {
                result += '\n';
              }
            } else if (typeof readline == 'function') {
              // Command line.
              result = readline();
              if (result !== null) {
                result += '\n';
              }
            }
            if (!result) {
              return null;
            }
            tty.input = intArrayFromString(result, true);
          }
          return tty.input.shift();
        },put_char:function (tty, val) {
          if (val === null || val === 10) {
            Module['print'](tty.output.join(''));
            tty.output = [];
          } else {
            tty.output.push(TTY.utf8.processCChar(val));
          }
        }},default_tty1_ops:{put_char:function (tty, val) {
          if (val === null || val === 10) {
            Module['printErr'](tty.output.join(''));
            tty.output = [];
          } else {
            tty.output.push(TTY.utf8.processCChar(val));
          }
        }}};

  var MEMFS={ops_table:null,CONTENT_OWNING:1,CONTENT_FLEXIBLE:2,CONTENT_FIXED:3,mount:function (mount) {
        return MEMFS.createNode(null, '/', 16384 | 511 /* 0777 */, 0);
      },createNode:function (parent, name, mode, dev) {
        if (FS.isBlkdev(mode) || FS.isFIFO(mode)) {
          // no supported
          throw new FS.ErrnoError(ERRNO_CODES.EPERM);
        }
        if (!MEMFS.ops_table) {
          MEMFS.ops_table = {
            dir: {
              node: {
                getattr: MEMFS.node_ops.getattr,
                setattr: MEMFS.node_ops.setattr,
                lookup: MEMFS.node_ops.lookup,
                mknod: MEMFS.node_ops.mknod,
                rename: MEMFS.node_ops.rename,
                unlink: MEMFS.node_ops.unlink,
                rmdir: MEMFS.node_ops.rmdir,
                readdir: MEMFS.node_ops.readdir,
                symlink: MEMFS.node_ops.symlink
              },
              stream: {
                llseek: MEMFS.stream_ops.llseek
              }
            },
            file: {
              node: {
                getattr: MEMFS.node_ops.getattr,
                setattr: MEMFS.node_ops.setattr
              },
              stream: {
                llseek: MEMFS.stream_ops.llseek,
                read: MEMFS.stream_ops.read,
                write: MEMFS.stream_ops.write,
                allocate: MEMFS.stream_ops.allocate,
                mmap: MEMFS.stream_ops.mmap
              }
            },
            link: {
              node: {
                getattr: MEMFS.node_ops.getattr,
                setattr: MEMFS.node_ops.setattr,
                readlink: MEMFS.node_ops.readlink
              },
              stream: {}
            },
            chrdev: {
              node: {
                getattr: MEMFS.node_ops.getattr,
                setattr: MEMFS.node_ops.setattr
              },
              stream: FS.chrdev_stream_ops
            },
          };
        }
        var node = FS.createNode(parent, name, mode, dev);
        if (FS.isDir(node.mode)) {
          node.node_ops = MEMFS.ops_table.dir.node;
          node.stream_ops = MEMFS.ops_table.dir.stream;
          node.contents = {};
        } else if (FS.isFile(node.mode)) {
          node.node_ops = MEMFS.ops_table.file.node;
          node.stream_ops = MEMFS.ops_table.file.stream;
          node.contents = [];
          node.contentMode = MEMFS.CONTENT_FLEXIBLE;
        } else if (FS.isLink(node.mode)) {
          node.node_ops = MEMFS.ops_table.link.node;
          node.stream_ops = MEMFS.ops_table.link.stream;
        } else if (FS.isChrdev(node.mode)) {
          node.node_ops = MEMFS.ops_table.chrdev.node;
          node.stream_ops = MEMFS.ops_table.chrdev.stream;
        }
        node.timestamp = Date.now();
        // add the new node to the parent
        if (parent) {
          parent.contents[name] = node;
        }
        return node;
      },ensureFlexible:function (node) {
        if (node.contentMode !== MEMFS.CONTENT_FLEXIBLE) {
          var contents = node.contents;
          node.contents = Array.prototype.slice.call(contents);
          node.contentMode = MEMFS.CONTENT_FLEXIBLE;
        }
      },node_ops:{getattr:function (node) {
          var attr = {};
          // device numbers reuse inode numbers.
          attr.dev = FS.isChrdev(node.mode) ? node.id : 1;
          attr.ino = node.id;
          attr.mode = node.mode;
          attr.nlink = 1;
          attr.uid = 0;
          attr.gid = 0;
          attr.rdev = node.rdev;
          if (FS.isDir(node.mode)) {
            attr.size = 4096;
          } else if (FS.isFile(node.mode)) {
            attr.size = node.contents.length;
          } else if (FS.isLink(node.mode)) {
            attr.size = node.link.length;
          } else {
            attr.size = 0;
          }
          attr.atime = new Date(node.timestamp);
          attr.mtime = new Date(node.timestamp);
          attr.ctime = new Date(node.timestamp);
          // NOTE: In our implementation, st_blocks = Math.ceil(st_size/st_blksize),
          //       but this is not required by the standard.
          attr.blksize = 4096;
          attr.blocks = Math.ceil(attr.size / attr.blksize);
          return attr;
        },setattr:function (node, attr) {
          if (attr.mode !== undefined) {
            node.mode = attr.mode;
          }
          if (attr.timestamp !== undefined) {
            node.timestamp = attr.timestamp;
          }
          if (attr.size !== undefined) {
            MEMFS.ensureFlexible(node);
            var contents = node.contents;
            if (attr.size < contents.length) contents.length = attr.size;
            else while (attr.size > contents.length) contents.push(0);
          }
        },lookup:function (parent, name) {
          throw FS.genericErrors[ERRNO_CODES.ENOENT];
        },mknod:function (parent, name, mode, dev) {
          return MEMFS.createNode(parent, name, mode, dev);
        },rename:function (old_node, new_dir, new_name) {
          // if we're overwriting a directory at new_name, make sure it's empty.
          if (FS.isDir(old_node.mode)) {
            var new_node;
            try {
              new_node = FS.lookupNode(new_dir, new_name);
            } catch (e) {
            }
            if (new_node) {
              for (var i in new_node.contents) {
                throw new FS.ErrnoError(ERRNO_CODES.ENOTEMPTY);
              }
            }
          }
          // do the internal rewiring
          delete old_node.parent.contents[old_node.name];
          old_node.name = new_name;
          new_dir.contents[new_name] = old_node;
          old_node.parent = new_dir;
        },unlink:function (parent, name) {
          delete parent.contents[name];
        },rmdir:function (parent, name) {
          var node = FS.lookupNode(parent, name);
          for (var i in node.contents) {
            throw new FS.ErrnoError(ERRNO_CODES.ENOTEMPTY);
          }
          delete parent.contents[name];
        },readdir:function (node) {
          var entries = ['.', '..']
          for (var key in node.contents) {
            if (!node.contents.hasOwnProperty(key)) {
              continue;
            }
            entries.push(key);
          }
          return entries;
        },symlink:function (parent, newname, oldpath) {
          var node = MEMFS.createNode(parent, newname, 511 /* 0777 */ | 40960, 0);
          node.link = oldpath;
          return node;
        },readlink:function (node) {
          if (!FS.isLink(node.mode)) {
            throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
          }
          return node.link;
        }},stream_ops:{read:function (stream, buffer, offset, length, position) {
          var contents = stream.node.contents;
          if (position >= contents.length)
            return 0;
          var size = Math.min(contents.length - position, length);
          assert(size >= 0);
          if (size > 8 && contents.subarray) { // non-trivial, and typed array
            buffer.set(contents.subarray(position, position + size), offset);
          } else
          {
            for (var i = 0; i < size; i++) {
              buffer[offset + i] = contents[position + i];
            }
          }
          return size;
        },write:function (stream, buffer, offset, length, position, canOwn) {
          var node = stream.node;
          node.timestamp = Date.now();
          var contents = node.contents;
          if (length && contents.length === 0 && position === 0 && buffer.subarray) {
            // just replace it with the new data
            if (canOwn && offset === 0) {
              node.contents = buffer; // this could be a subarray of Emscripten HEAP, or allocated from some other source.
              node.contentMode = (buffer.buffer === HEAP8.buffer) ? MEMFS.CONTENT_OWNING : MEMFS.CONTENT_FIXED;
            } else {
              node.contents = new Uint8Array(buffer.subarray(offset, offset+length));
              node.contentMode = MEMFS.CONTENT_FIXED;
            }
            return length;
          }
          MEMFS.ensureFlexible(node);
          var contents = node.contents;
          while (contents.length < position) contents.push(0);
          for (var i = 0; i < length; i++) {
            contents[position + i] = buffer[offset + i];
          }
          return length;
        },llseek:function (stream, offset, whence) {
          var position = offset;
          if (whence === 1) {  // SEEK_CUR.
            position += stream.position;
          } else if (whence === 2) {  // SEEK_END.
            if (FS.isFile(stream.node.mode)) {
              position += stream.node.contents.length;
            }
          }
          if (position < 0) {
            throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
          }
          stream.ungotten = [];
          stream.position = position;
          return position;
        },allocate:function (stream, offset, length) {
          MEMFS.ensureFlexible(stream.node);
          var contents = stream.node.contents;
          var limit = offset + length;
          while (limit > contents.length) contents.push(0);
        },mmap:function (stream, buffer, offset, length, position, prot, flags) {
          if (!FS.isFile(stream.node.mode)) {
            throw new FS.ErrnoError(ERRNO_CODES.ENODEV);
          }
          var ptr;
          var allocated;
          var contents = stream.node.contents;
          // Only make a new copy when MAP_PRIVATE is specified.
          if ( !(flags & 2) &&
                (contents.buffer === buffer || contents.buffer === buffer.buffer) ) {
            // We can't emulate MAP_SHARED when the file is not backed by the buffer
            // we're mapping to (e.g. the HEAP buffer).
            allocated = false;
            ptr = contents.byteOffset;
          } else {
            // Try to avoid unnecessary slices.
            if (position > 0 || position + length < contents.length) {
              if (contents.subarray) {
                contents = contents.subarray(position, position + length);
              } else {
                contents = Array.prototype.slice.call(contents, position, position + length);
              }
            }
            allocated = true;
            ptr = _malloc(length);
            if (!ptr) {
              throw new FS.ErrnoError(ERRNO_CODES.ENOMEM);
            }
            buffer.set(contents, ptr);
          }
          return { ptr: ptr, allocated: allocated };
        }}};

  var IDBFS={dbs:{},indexedDB:function () {
        return window.indexedDB || window.mozIndexedDB || window.webkitIndexedDB || window.msIndexedDB;
      },DB_VERSION:21,DB_STORE_NAME:"FILE_DATA",mount:function (mount) {
        // reuse all of the core MEMFS functionality
        return MEMFS.mount.apply(null, arguments);
      },syncfs:function (mount, populate, callback) {
        IDBFS.getLocalSet(mount, function(err, local) {
          if (err) return callback(err);

          IDBFS.getRemoteSet(mount, function(err, remote) {
            if (err) return callback(err);

            var src = populate ? remote : local;
            var dst = populate ? local : remote;

            IDBFS.reconcile(src, dst, callback);
          });
        });
      },getDB:function (name, callback) {
        // check the cache first
        var db = IDBFS.dbs[name];
        if (db) {
          return callback(null, db);
        }

        var req;
        try {
          req = IDBFS.indexedDB().open(name, IDBFS.DB_VERSION);
        } catch (e) {
          return callback(e);
        }
        req.onupgradeneeded = function(e) {
          var db = e.target.result;
          var transaction = e.target.transaction;

          var fileStore;

          if (db.objectStoreNames.contains(IDBFS.DB_STORE_NAME)) {
            fileStore = transaction.objectStore(IDBFS.DB_STORE_NAME);
          } else {
            fileStore = db.createObjectStore(IDBFS.DB_STORE_NAME);
          }

          fileStore.createIndex('timestamp', 'timestamp', { unique: false });
        };
        req.onsuccess = function() {
          db = req.result;

          // add to the cache
          IDBFS.dbs[name] = db;
          callback(null, db);
        };
        req.onerror = function() {
          callback(this.error);
        };
      },getLocalSet:function (mount, callback) {
        var entries = {};

        function isRealDir(p) {
          return p !== '.' && p !== '..';
        };
        function toAbsolute(root) {
          return function(p) {
            return PATH.join2(root, p);
          }
        };

        var check = FS.readdir(mount.mountpoint).filter(isRealDir).map(toAbsolute(mount.mountpoint));

        while (check.length) {
          var path = check.pop();
          var stat;

          try {
            stat = FS.stat(path);
          } catch (e) {
            return callback(e);
          }

          if (FS.isDir(stat.mode)) {
            check.push.apply(check, FS.readdir(path).filter(isRealDir).map(toAbsolute(path)));
          }

          entries[path] = { timestamp: stat.mtime };
        }

        return callback(null, { type: 'local', entries: entries });
      },getRemoteSet:function (mount, callback) {
        var entries = {};

        IDBFS.getDB(mount.mountpoint, function(err, db) {
          if (err) return callback(err);

          var transaction = db.transaction([IDBFS.DB_STORE_NAME], 'readonly');
          transaction.onerror = function() { callback(this.error); };

          var store = transaction.objectStore(IDBFS.DB_STORE_NAME);
          var index = store.index('timestamp');

          index.openKeyCursor().onsuccess = function(event) {
            var cursor = event.target.result;

            if (!cursor) {
              return callback(null, { type: 'remote', db: db, entries: entries });
            }

            entries[cursor.primaryKey] = { timestamp: cursor.key };

            cursor.continue();
          };
        });
      },loadLocalEntry:function (path, callback) {
        var stat, node;

        try {
          var lookup = FS.lookupPath(path);
          node = lookup.node;
          stat = FS.stat(path);
        } catch (e) {
          return callback(e);
        }

        if (FS.isDir(stat.mode)) {
          return callback(null, { timestamp: stat.mtime, mode: stat.mode });
        } else if (FS.isFile(stat.mode)) {
          return callback(null, { timestamp: stat.mtime, mode: stat.mode, contents: node.contents });
        } else {
          return callback(new Error('node type not supported'));
        }
      },storeLocalEntry:function (path, entry, callback) {
        try {
          if (FS.isDir(entry.mode)) {
            FS.mkdir(path, entry.mode);
          } else if (FS.isFile(entry.mode)) {
            FS.writeFile(path, entry.contents, { encoding: 'binary', canOwn: true });
          } else {
            return callback(new Error('node type not supported'));
          }

          FS.utime(path, entry.timestamp, entry.timestamp);
        } catch (e) {
          return callback(e);
        }

        callback(null);
      },removeLocalEntry:function (path, callback) {
        try {
          var lookup = FS.lookupPath(path);
          var stat = FS.stat(path);

          if (FS.isDir(stat.mode)) {
            FS.rmdir(path);
          } else if (FS.isFile(stat.mode)) {
            FS.unlink(path);
          }
        } catch (e) {
          return callback(e);
        }

        callback(null);
      },loadRemoteEntry:function (store, path, callback) {
        var req = store.get(path);
        req.onsuccess = function(event) { callback(null, event.target.result); };
        req.onerror = function() { callback(this.error); };
      },storeRemoteEntry:function (store, path, entry, callback) {
        var req = store.put(entry, path);
        req.onsuccess = function() { callback(null); };
        req.onerror = function() { callback(this.error); };
      },removeRemoteEntry:function (store, path, callback) {
        var req = store.delete(path);
        req.onsuccess = function() { callback(null); };
        req.onerror = function() { callback(this.error); };
      },reconcile:function (src, dst, callback) {
        var total = 0;

        var create = [];
        Object.keys(src.entries).forEach(function (key) {
          var e = src.entries[key];
          var e2 = dst.entries[key];
          if (!e2 || e.timestamp > e2.timestamp) {
            create.push(key);
            total++;
          }
        });

        var remove = [];
        Object.keys(dst.entries).forEach(function (key) {
          var e = dst.entries[key];
          var e2 = src.entries[key];
          if (!e2) {
            remove.push(key);
            total++;
          }
        });

        if (!total) {
          return callback(null);
        }

        var errored = false;
        var completed = 0;
        var db = src.type === 'remote' ? src.db : dst.db;
        var transaction = db.transaction([IDBFS.DB_STORE_NAME], 'readwrite');
        var store = transaction.objectStore(IDBFS.DB_STORE_NAME);

        function done(err) {
          if (err) {
            if (!done.errored) {
              done.errored = true;
              return callback(err);
            }
            return;
          }
          if (++completed >= total) {
            return callback(null);
          }
        };

        transaction.onerror = function() { done(this.error); };

        // sort paths in ascending order so directory entries are created
        // before the files inside them
        create.sort().forEach(function (path) {
          if (dst.type === 'local') {
            IDBFS.loadRemoteEntry(store, path, function (err, entry) {
              if (err) return done(err);
              IDBFS.storeLocalEntry(path, entry, done);
            });
          } else {
            IDBFS.loadLocalEntry(path, function (err, entry) {
              if (err) return done(err);
              IDBFS.storeRemoteEntry(store, path, entry, done);
            });
          }
        });

        // sort paths in descending order so files are deleted before their
        // parent directories
        remove.sort().reverse().forEach(function(path) {
          if (dst.type === 'local') {
            IDBFS.removeLocalEntry(path, done);
          } else {
            IDBFS.removeRemoteEntry(store, path, done);
          }
        });
      }};

  var NODEFS={isWindows:false,staticInit:function () {
        NODEFS.isWindows = !!process.platform.match(/^win/);
      },mount:function (mount) {
        assert(ENVIRONMENT_IS_NODE);
        return NODEFS.createNode(null, '/', NODEFS.getMode(mount.opts.root), 0);
      },createNode:function (parent, name, mode, dev) {
        if (!FS.isDir(mode) && !FS.isFile(mode) && !FS.isLink(mode)) {
          throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
        }
        var node = FS.createNode(parent, name, mode);
        node.node_ops = NODEFS.node_ops;
        node.stream_ops = NODEFS.stream_ops;
        return node;
      },getMode:function (path) {
        var stat;
        try {
          stat = fs.lstatSync(path);
          if (NODEFS.isWindows) {
            // On Windows, directories return permission bits 'rw-rw-rw-', even though they have 'rwxrwxrwx', so
            // propagate write bits to execute bits.
            stat.mode = stat.mode | ((stat.mode & 146) >> 1);
          }
        } catch (e) {
          if (!e.code) throw e;
          throw new FS.ErrnoError(ERRNO_CODES[e.code]);
        }
        return stat.mode;
      },realPath:function (node) {
        var parts = [];
        while (node.parent !== node) {
          parts.push(node.name);
          node = node.parent;
        }
        parts.push(node.mount.opts.root);
        parts.reverse();
        return PATH.join.apply(null, parts);
      },flagsToPermissionStringMap:{0:"r",1:"r+",2:"r+",64:"r",65:"r+",66:"r+",129:"rx+",193:"rx+",514:"w+",577:"w",578:"w+",705:"wx",706:"wx+",1024:"a",1025:"a",1026:"a+",1089:"a",1090:"a+",1153:"ax",1154:"ax+",1217:"ax",1218:"ax+",4096:"rs",4098:"rs+"},flagsToPermissionString:function (flags) {
        if (flags in NODEFS.flagsToPermissionStringMap) {
          return NODEFS.flagsToPermissionStringMap[flags];
        } else {
          return flags;
        }
      },node_ops:{getattr:function (node) {
          var path = NODEFS.realPath(node);
          var stat;
          try {
            stat = fs.lstatSync(path);
          } catch (e) {
            if (!e.code) throw e;
            throw new FS.ErrnoError(ERRNO_CODES[e.code]);
          }
          // node.js v0.10.20 doesn't report blksize and blocks on Windows. Fake them with default blksize of 4096.
          // See http://support.microsoft.com/kb/140365
          if (NODEFS.isWindows && !stat.blksize) {
            stat.blksize = 4096;
          }
          if (NODEFS.isWindows && !stat.blocks) {
            stat.blocks = (stat.size+stat.blksize-1)/stat.blksize|0;
          }
          return {
            dev: stat.dev,
            ino: stat.ino,
            mode: stat.mode,
            nlink: stat.nlink,
            uid: stat.uid,
            gid: stat.gid,
            rdev: stat.rdev,
            size: stat.size,
            atime: stat.atime,
            mtime: stat.mtime,
            ctime: stat.ctime,
            blksize: stat.blksize,
            blocks: stat.blocks
          };
        },setattr:function (node, attr) {
          var path = NODEFS.realPath(node);
          try {
            if (attr.mode !== undefined) {
              fs.chmodSync(path, attr.mode);
              // update the common node structure mode as well
              node.mode = attr.mode;
            }
            if (attr.timestamp !== undefined) {
              var date = new Date(attr.timestamp);
              fs.utimesSync(path, date, date);
            }
            if (attr.size !== undefined) {
              fs.truncateSync(path, attr.size);
            }
          } catch (e) {
            if (!e.code) throw e;
            throw new FS.ErrnoError(ERRNO_CODES[e.code]);
          }
        },lookup:function (parent, name) {
          var path = PATH.join2(NODEFS.realPath(parent), name);
          var mode = NODEFS.getMode(path);
          return NODEFS.createNode(parent, name, mode);
        },mknod:function (parent, name, mode, dev) {
          var node = NODEFS.createNode(parent, name, mode, dev);
          // create the backing node for this in the fs root as well
          var path = NODEFS.realPath(node);
          try {
            if (FS.isDir(node.mode)) {
              fs.mkdirSync(path, node.mode);
            } else {
              fs.writeFileSync(path, '', { mode: node.mode });
            }
          } catch (e) {
            if (!e.code) throw e;
            throw new FS.ErrnoError(ERRNO_CODES[e.code]);
          }
          return node;
        },rename:function (oldNode, newDir, newName) {
          var oldPath = NODEFS.realPath(oldNode);
          var newPath = PATH.join2(NODEFS.realPath(newDir), newName);
          try {
            fs.renameSync(oldPath, newPath);
          } catch (e) {
            if (!e.code) throw e;
            throw new FS.ErrnoError(ERRNO_CODES[e.code]);
          }
        },unlink:function (parent, name) {
          var path = PATH.join2(NODEFS.realPath(parent), name);
          try {
            fs.unlinkSync(path);
          } catch (e) {
            if (!e.code) throw e;
            throw new FS.ErrnoError(ERRNO_CODES[e.code]);
          }
        },rmdir:function (parent, name) {
          var path = PATH.join2(NODEFS.realPath(parent), name);
          try {
            fs.rmdirSync(path);
          } catch (e) {
            if (!e.code) throw e;
            throw new FS.ErrnoError(ERRNO_CODES[e.code]);
          }
        },readdir:function (node) {
          var path = NODEFS.realPath(node);
          try {
            return fs.readdirSync(path);
          } catch (e) {
            if (!e.code) throw e;
            throw new FS.ErrnoError(ERRNO_CODES[e.code]);
          }
        },symlink:function (parent, newName, oldPath) {
          var newPath = PATH.join2(NODEFS.realPath(parent), newName);
          try {
            fs.symlinkSync(oldPath, newPath);
          } catch (e) {
            if (!e.code) throw e;
            throw new FS.ErrnoError(ERRNO_CODES[e.code]);
          }
        },readlink:function (node) {
          var path = NODEFS.realPath(node);
          try {
            return fs.readlinkSync(path);
          } catch (e) {
            if (!e.code) throw e;
            throw new FS.ErrnoError(ERRNO_CODES[e.code]);
          }
        }},stream_ops:{open:function (stream) {
          var path = NODEFS.realPath(stream.node);
          try {
            if (FS.isFile(stream.node.mode)) {
              stream.nfd = fs.openSync(path, NODEFS.flagsToPermissionString(stream.flags));
            }
          } catch (e) {
            if (!e.code) throw e;
            throw new FS.ErrnoError(ERRNO_CODES[e.code]);
          }
        },close:function (stream) {
          try {
            if (FS.isFile(stream.node.mode) && stream.nfd) {
              fs.closeSync(stream.nfd);
            }
          } catch (e) {
            if (!e.code) throw e;
            throw new FS.ErrnoError(ERRNO_CODES[e.code]);
          }
        },read:function (stream, buffer, offset, length, position) {
          // FIXME this is terrible.
          var nbuffer = new Buffer(length);
          var res;
          try {
            res = fs.readSync(stream.nfd, nbuffer, 0, length, position);
          } catch (e) {
            throw new FS.ErrnoError(ERRNO_CODES[e.code]);
          }
          if (res > 0) {
            for (var i = 0; i < res; i++) {
              buffer[offset + i] = nbuffer[i];
            }
          }
          return res;
        },write:function (stream, buffer, offset, length, position) {
          // FIXME this is terrible.
          var nbuffer = new Buffer(buffer.subarray(offset, offset + length));
          var res;
          try {
            res = fs.writeSync(stream.nfd, nbuffer, 0, length, position);
          } catch (e) {
            throw new FS.ErrnoError(ERRNO_CODES[e.code]);
          }
          return res;
        },llseek:function (stream, offset, whence) {
          var position = offset;
          if (whence === 1) {  // SEEK_CUR.
            position += stream.position;
          } else if (whence === 2) {  // SEEK_END.
            if (FS.isFile(stream.node.mode)) {
              try {
                var stat = fs.fstatSync(stream.nfd);
                position += stat.size;
              } catch (e) {
                throw new FS.ErrnoError(ERRNO_CODES[e.code]);
              }
            }
          }

          if (position < 0) {
            throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
          }

          stream.position = position;
          return position;
        }}};

  var _stdin=allocate(1, "i32*", ALLOC_STATIC);

  var _stdout=allocate(1, "i32*", ALLOC_STATIC);

  var _stderr=allocate(1, "i32*", ALLOC_STATIC);

  function _fflush(stream) {
      // int fflush(FILE *stream);
      // http://pubs.opengroup.org/onlinepubs/000095399/functions/fflush.html
      // we don't currently perform any user-space buffering of data
    }var FS={root:null,mounts:[],devices:[null],streams:[],nextInode:1,nameTable:null,currentPath:"/",initialized:false,ignorePermissions:true,ErrnoError:null,genericErrors:{},handleFSError:function (e) {
        if (!(e instanceof FS.ErrnoError)) throw e + ' : ' + stackTrace();
        return ___setErrNo(e.errno);
      },lookupPath:function (path, opts) {
        path = PATH.resolve(FS.cwd(), path);
        opts = opts || {};

        var defaults = {
          follow_mount: true,
          recurse_count: 0
        };
        for (var key in defaults) {
          if (opts[key] === undefined) {
            opts[key] = defaults[key];
          }
        }

        if (opts.recurse_count > 8) {  // max recursive lookup of 8
          throw new FS.ErrnoError(ERRNO_CODES.ELOOP);
        }

        // split the path
        var parts = PATH.normalizeArray(path.split('/').filter(function(p) {
          return !!p;
        }), false);

        // start at the root
        var current = FS.root;
        var current_path = '/';

        for (var i = 0; i < parts.length; i++) {
          var islast = (i === parts.length-1);
          if (islast && opts.parent) {
            // stop resolving
            break;
          }

          current = FS.lookupNode(current, parts[i]);
          current_path = PATH.join2(current_path, parts[i]);

          // jump to the mount's root node if this is a mountpoint
          if (FS.isMountpoint(current)) {
            if (!islast || (islast && opts.follow_mount)) {
              current = current.mounted.root;
            }
          }

          // by default, lookupPath will not follow a symlink if it is the final path component.
          // setting opts.follow = true will override this behavior.
          if (!islast || opts.follow) {
            var count = 0;
            while (FS.isLink(current.mode)) {
              var link = FS.readlink(current_path);
              current_path = PATH.resolve(PATH.dirname(current_path), link);

              var lookup = FS.lookupPath(current_path, { recurse_count: opts.recurse_count });
              current = lookup.node;

              if (count++ > 40) {  // limit max consecutive symlinks to 40 (SYMLOOP_MAX).
                throw new FS.ErrnoError(ERRNO_CODES.ELOOP);
              }
            }
          }
        }

        return { path: current_path, node: current };
      },getPath:function (node) {
        var path;
        while (true) {
          if (FS.isRoot(node)) {
            var mount = node.mount.mountpoint;
            if (!path) return mount;
            return mount[mount.length-1] !== '/' ? mount + '/' + path : mount + path;
          }
          path = path ? node.name + '/' + path : node.name;
          node = node.parent;
        }
      },hashName:function (parentid, name) {
        var hash = 0;


        for (var i = 0; i < name.length; i++) {
          hash = ((hash << 5) - hash + name.charCodeAt(i)) | 0;
        }
        return ((parentid + hash) >>> 0) % FS.nameTable.length;
      },hashAddNode:function (node) {
        var hash = FS.hashName(node.parent.id, node.name);
        node.name_next = FS.nameTable[hash];
        FS.nameTable[hash] = node;
      },hashRemoveNode:function (node) {
        var hash = FS.hashName(node.parent.id, node.name);
        if (FS.nameTable[hash] === node) {
          FS.nameTable[hash] = node.name_next;
        } else {
          var current = FS.nameTable[hash];
          while (current) {
            if (current.name_next === node) {
              current.name_next = node.name_next;
              break;
            }
            current = current.name_next;
          }
        }
      },lookupNode:function (parent, name) {
        var err = FS.mayLookup(parent);
        if (err) {
          throw new FS.ErrnoError(err);
        }
        var hash = FS.hashName(parent.id, name);
        for (var node = FS.nameTable[hash]; node; node = node.name_next) {
          var nodeName = node.name;
          if (node.parent.id === parent.id && nodeName === name) {
            return node;
          }
        }
        // if we failed to find it in the cache, call into the VFS
        return FS.lookup(parent, name);
      },createNode:function (parent, name, mode, rdev) {
        if (!FS.FSNode) {
          FS.FSNode = function(parent, name, mode, rdev) {
            if (!parent) {
              parent = this;  // root node sets parent to itself
            }
            this.parent = parent;
            this.mount = parent.mount;
            this.mounted = null;
            this.id = FS.nextInode++;
            this.name = name;
            this.mode = mode;
            this.node_ops = {};
            this.stream_ops = {};
            this.rdev = rdev;
          };

          FS.FSNode.prototype = {};

          // compatibility
          var readMode = 292 | 73;
          var writeMode = 146;

          // NOTE we must use Object.defineProperties instead of individual calls to
          // Object.defineProperty in order to make closure compiler happy
          Object.defineProperties(FS.FSNode.prototype, {
            read: {
              get: function() { return (this.mode & readMode) === readMode; },
              set: function(val) { val ? this.mode |= readMode : this.mode &= ~readMode; }
            },
            write: {
              get: function() { return (this.mode & writeMode) === writeMode; },
              set: function(val) { val ? this.mode |= writeMode : this.mode &= ~writeMode; }
            },
            isFolder: {
              get: function() { return FS.isDir(this.mode); },
            },
            isDevice: {
              get: function() { return FS.isChrdev(this.mode); },
            },
          });
        }

        var node = new FS.FSNode(parent, name, mode, rdev);

        FS.hashAddNode(node);

        return node;
      },destroyNode:function (node) {
        FS.hashRemoveNode(node);
      },isRoot:function (node) {
        return node === node.parent;
      },isMountpoint:function (node) {
        return !!node.mounted;
      },isFile:function (mode) {
        return (mode & 61440) === 32768;
      },isDir:function (mode) {
        return (mode & 61440) === 16384;
      },isLink:function (mode) {
        return (mode & 61440) === 40960;
      },isChrdev:function (mode) {
        return (mode & 61440) === 8192;
      },isBlkdev:function (mode) {
        return (mode & 61440) === 24576;
      },isFIFO:function (mode) {
        return (mode & 61440) === 4096;
      },isSocket:function (mode) {
        return (mode & 49152) === 49152;
      },flagModes:{"r":0,"rs":1052672,"r+":2,"w":577,"wx":705,"xw":705,"w+":578,"wx+":706,"xw+":706,"a":1089,"ax":1217,"xa":1217,"a+":1090,"ax+":1218,"xa+":1218},modeStringToFlags:function (str) {
        var flags = FS.flagModes[str];
        if (typeof flags === 'undefined') {
          throw new Error('Unknown file open mode: ' + str);
        }
        return flags;
      },flagsToPermissionString:function (flag) {
        var accmode = flag & 2097155;
        var perms = ['r', 'w', 'rw'][accmode];
        if ((flag & 512)) {
          perms += 'w';
        }
        return perms;
      },nodePermissions:function (node, perms) {
        if (FS.ignorePermissions) {
          return 0;
        }
        // return 0 if any user, group or owner bits are set.
        if (perms.indexOf('r') !== -1 && !(node.mode & 292)) {
          return ERRNO_CODES.EACCES;
        } else if (perms.indexOf('w') !== -1 && !(node.mode & 146)) {
          return ERRNO_CODES.EACCES;
        } else if (perms.indexOf('x') !== -1 && !(node.mode & 73)) {
          return ERRNO_CODES.EACCES;
        }
        return 0;
      },mayLookup:function (dir) {
        return FS.nodePermissions(dir, 'x');
      },mayCreate:function (dir, name) {
        try {
          var node = FS.lookupNode(dir, name);
          return ERRNO_CODES.EEXIST;
        } catch (e) {
        }
        return FS.nodePermissions(dir, 'wx');
      },mayDelete:function (dir, name, isdir) {
        var node;
        try {
          node = FS.lookupNode(dir, name);
        } catch (e) {
          return e.errno;
        }
        var err = FS.nodePermissions(dir, 'wx');
        if (err) {
          return err;
        }
        if (isdir) {
          if (!FS.isDir(node.mode)) {
            return ERRNO_CODES.ENOTDIR;
          }
          if (FS.isRoot(node) || FS.getPath(node) === FS.cwd()) {
            return ERRNO_CODES.EBUSY;
          }
        } else {
          if (FS.isDir(node.mode)) {
            return ERRNO_CODES.EISDIR;
          }
        }
        return 0;
      },mayOpen:function (node, flags) {
        if (!node) {
          return ERRNO_CODES.ENOENT;
        }
        if (FS.isLink(node.mode)) {
          return ERRNO_CODES.ELOOP;
        } else if (FS.isDir(node.mode)) {
          if ((flags & 2097155) !== 0 ||  // opening for write
              (flags & 512)) {
            return ERRNO_CODES.EISDIR;
          }
        }
        return FS.nodePermissions(node, FS.flagsToPermissionString(flags));
      },MAX_OPEN_FDS:4096,nextfd:function (fd_start, fd_end) {
        fd_start = fd_start || 0;
        fd_end = fd_end || FS.MAX_OPEN_FDS;
        for (var fd = fd_start; fd <= fd_end; fd++) {
          if (!FS.streams[fd]) {
            return fd;
          }
        }
        throw new FS.ErrnoError(ERRNO_CODES.EMFILE);
      },getStream:function (fd) {
        return FS.streams[fd];
      },createStream:function (stream, fd_start, fd_end) {
        if (!FS.FSStream) {
          FS.FSStream = function(){};
          FS.FSStream.prototype = {};
          // compatibility
          Object.defineProperties(FS.FSStream.prototype, {
            object: {
              get: function() { return this.node; },
              set: function(val) { this.node = val; }
            },
            isRead: {
              get: function() { return (this.flags & 2097155) !== 1; }
            },
            isWrite: {
              get: function() { return (this.flags & 2097155) !== 0; }
            },
            isAppend: {
              get: function() { return (this.flags & 1024); }
            }
          });
        }
        // clone it, so we can return an instance of FSStream
        var newStream = new FS.FSStream();
        for (var p in stream) {
          newStream[p] = stream[p];
        }
        stream = newStream;
        var fd = FS.nextfd(fd_start, fd_end);
        stream.fd = fd;
        FS.streams[fd] = stream;
        return stream;
      },closeStream:function (fd) {
        FS.streams[fd] = null;
      },getStreamFromPtr:function (ptr) {
        return FS.streams[ptr - 1];
      },getPtrForStream:function (stream) {
        return stream ? stream.fd + 1 : 0;
      },chrdev_stream_ops:{open:function (stream) {
          var device = FS.getDevice(stream.node.rdev);
          // override node's stream ops with the device's
          stream.stream_ops = device.stream_ops;
          // forward the open call
          if (stream.stream_ops.open) {
            stream.stream_ops.open(stream);
          }
        },llseek:function () {
          throw new FS.ErrnoError(ERRNO_CODES.ESPIPE);
        }},major:function (dev) {
        return ((dev) >> 8);
      },minor:function (dev) {
        return ((dev) & 0xff);
      },makedev:function (ma, mi) {
        return ((ma) << 8 | (mi));
      },registerDevice:function (dev, ops) {
        FS.devices[dev] = { stream_ops: ops };
      },getDevice:function (dev) {
        return FS.devices[dev];
      },getMounts:function (mount) {
        var mounts = [];
        var check = [mount];

        while (check.length) {
          var m = check.pop();

          mounts.push(m);

          check.push.apply(check, m.mounts);
        }

        return mounts;
      },syncfs:function (populate, callback) {
        if (typeof(populate) === 'function') {
          callback = populate;
          populate = false;
        }

        var mounts = FS.getMounts(FS.root.mount);
        var completed = 0;

        function done(err) {
          if (err) {
            if (!done.errored) {
              done.errored = true;
              return callback(err);
            }
            return;
          }
          if (++completed >= mounts.length) {
            callback(null);
          }
        };

        // sync all mounts
        mounts.forEach(function (mount) {
          if (!mount.type.syncfs) {
            return done(null);
          }
          mount.type.syncfs(mount, populate, done);
        });
      },mount:function (type, opts, mountpoint) {
        var root = mountpoint === '/';
        var pseudo = !mountpoint;
        var node;

        if (root && FS.root) {
          throw new FS.ErrnoError(ERRNO_CODES.EBUSY);
        } else if (!root && !pseudo) {
          var lookup = FS.lookupPath(mountpoint, { follow_mount: false });

          mountpoint = lookup.path;  // use the absolute path
          node = lookup.node;

          if (FS.isMountpoint(node)) {
            throw new FS.ErrnoError(ERRNO_CODES.EBUSY);
          }

          if (!FS.isDir(node.mode)) {
            throw new FS.ErrnoError(ERRNO_CODES.ENOTDIR);
          }
        }

        var mount = {
          type: type,
          opts: opts,
          mountpoint: mountpoint,
          mounts: []
        };

        // create a root node for the fs
        var mountRoot = type.mount(mount);
        mountRoot.mount = mount;
        mount.root = mountRoot;

        if (root) {
          FS.root = mountRoot;
        } else if (node) {
          // set as a mountpoint
          node.mounted = mount;

          // add the new mount to the current mount's children
          if (node.mount) {
            node.mount.mounts.push(mount);
          }
        }

        return mountRoot;
      },unmount:function (mountpoint) {
        var lookup = FS.lookupPath(mountpoint, { follow_mount: false });

        if (!FS.isMountpoint(lookup.node)) {
          throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
        }

        // destroy the nodes for this mount, and all its child mounts
        var node = lookup.node;
        var mount = node.mounted;
        var mounts = FS.getMounts(mount);

        Object.keys(FS.nameTable).forEach(function (hash) {
          var current = FS.nameTable[hash];

          while (current) {
            var next = current.name_next;

            if (mounts.indexOf(current.mount) !== -1) {
              FS.destroyNode(current);
            }

            current = next;
          }
        });

        // no longer a mountpoint
        node.mounted = null;

        // remove this mount from the child mounts
        var idx = node.mount.mounts.indexOf(mount);
        assert(idx !== -1);
        node.mount.mounts.splice(idx, 1);
      },lookup:function (parent, name) {
        return parent.node_ops.lookup(parent, name);
      },mknod:function (path, mode, dev) {
        var lookup = FS.lookupPath(path, { parent: true });
        var parent = lookup.node;
        var name = PATH.basename(path);
        var err = FS.mayCreate(parent, name);
        if (err) {
          throw new FS.ErrnoError(err);
        }
        if (!parent.node_ops.mknod) {
          throw new FS.ErrnoError(ERRNO_CODES.EPERM);
        }
        return parent.node_ops.mknod(parent, name, mode, dev);
      },create:function (path, mode) {
        mode = mode !== undefined ? mode : 438 /* 0666 */;
        mode &= 4095;
        mode |= 32768;
        return FS.mknod(path, mode, 0);
      },mkdir:function (path, mode) {
        mode = mode !== undefined ? mode : 511 /* 0777 */;
        mode &= 511 | 512;
        mode |= 16384;
        return FS.mknod(path, mode, 0);
      },mkdev:function (path, mode, dev) {
        if (typeof(dev) === 'undefined') {
          dev = mode;
          mode = 438 /* 0666 */;
        }
        mode |= 8192;
        return FS.mknod(path, mode, dev);
      },symlink:function (oldpath, newpath) {
        var lookup = FS.lookupPath(newpath, { parent: true });
        var parent = lookup.node;
        var newname = PATH.basename(newpath);
        var err = FS.mayCreate(parent, newname);
        if (err) {
          throw new FS.ErrnoError(err);
        }
        if (!parent.node_ops.symlink) {
          throw new FS.ErrnoError(ERRNO_CODES.EPERM);
        }
        return parent.node_ops.symlink(parent, newname, oldpath);
      },rename:function (old_path, new_path) {
        var old_dirname = PATH.dirname(old_path);
        var new_dirname = PATH.dirname(new_path);
        var old_name = PATH.basename(old_path);
        var new_name = PATH.basename(new_path);
        // parents must exist
        var lookup, old_dir, new_dir;
        try {
          lookup = FS.lookupPath(old_path, { parent: true });
          old_dir = lookup.node;
          lookup = FS.lookupPath(new_path, { parent: true });
          new_dir = lookup.node;
        } catch (e) {
          throw new FS.ErrnoError(ERRNO_CODES.EBUSY);
        }
        // need to be part of the same mount
        if (old_dir.mount !== new_dir.mount) {
          throw new FS.ErrnoError(ERRNO_CODES.EXDEV);
        }
        // source must exist
        var old_node = FS.lookupNode(old_dir, old_name);
        // old path should not be an ancestor of the new path
        var relative = PATH.relative(old_path, new_dirname);
        if (relative.charAt(0) !== '.') {
          throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
        }
        // new path should not be an ancestor of the old path
        relative = PATH.relative(new_path, old_dirname);
        if (relative.charAt(0) !== '.') {
          throw new FS.ErrnoError(ERRNO_CODES.ENOTEMPTY);
        }
        // see if the new path already exists
        var new_node;
        try {
          new_node = FS.lookupNode(new_dir, new_name);
        } catch (e) {
          // not fatal
        }
        // early out if nothing needs to change
        if (old_node === new_node) {
          return;
        }
        // we'll need to delete the old entry
        var isdir = FS.isDir(old_node.mode);
        var err = FS.mayDelete(old_dir, old_name, isdir);
        if (err) {
          throw new FS.ErrnoError(err);
        }
        // need delete permissions if we'll be overwriting.
        // need create permissions if new doesn't already exist.
        err = new_node ?
          FS.mayDelete(new_dir, new_name, isdir) :
          FS.mayCreate(new_dir, new_name);
        if (err) {
          throw new FS.ErrnoError(err);
        }
        if (!old_dir.node_ops.rename) {
          throw new FS.ErrnoError(ERRNO_CODES.EPERM);
        }
        if (FS.isMountpoint(old_node) || (new_node && FS.isMountpoint(new_node))) {
          throw new FS.ErrnoError(ERRNO_CODES.EBUSY);
        }
        // if we are going to change the parent, check write permissions
        if (new_dir !== old_dir) {
          err = FS.nodePermissions(old_dir, 'w');
          if (err) {
            throw new FS.ErrnoError(err);
          }
        }
        // remove the node from the lookup hash
        FS.hashRemoveNode(old_node);
        // do the underlying fs rename
        try {
          old_dir.node_ops.rename(old_node, new_dir, new_name);
        } catch (e) {
          throw e;
        } finally {
          // add the node back to the hash (in case node_ops.rename
          // changed its name)
          FS.hashAddNode(old_node);
        }
      },rmdir:function (path) {
        var lookup = FS.lookupPath(path, { parent: true });
        var parent = lookup.node;
        var name = PATH.basename(path);
        var node = FS.lookupNode(parent, name);
        var err = FS.mayDelete(parent, name, true);
        if (err) {
          throw new FS.ErrnoError(err);
        }
        if (!parent.node_ops.rmdir) {
          throw new FS.ErrnoError(ERRNO_CODES.EPERM);
        }
        if (FS.isMountpoint(node)) {
          throw new FS.ErrnoError(ERRNO_CODES.EBUSY);
        }
        parent.node_ops.rmdir(parent, name);
        FS.destroyNode(node);
      },readdir:function (path) {
        var lookup = FS.lookupPath(path, { follow: true });
        var node = lookup.node;
        if (!node.node_ops.readdir) {
          throw new FS.ErrnoError(ERRNO_CODES.ENOTDIR);
        }
        return node.node_ops.readdir(node);
      },unlink:function (path) {
        var lookup = FS.lookupPath(path, { parent: true });
        var parent = lookup.node;
        var name = PATH.basename(path);
        var node = FS.lookupNode(parent, name);
        var err = FS.mayDelete(parent, name, false);
        if (err) {
          // POSIX says unlink should set EPERM, not EISDIR
          if (err === ERRNO_CODES.EISDIR) err = ERRNO_CODES.EPERM;
          throw new FS.ErrnoError(err);
        }
        if (!parent.node_ops.unlink) {
          throw new FS.ErrnoError(ERRNO_CODES.EPERM);
        }
        if (FS.isMountpoint(node)) {
          throw new FS.ErrnoError(ERRNO_CODES.EBUSY);
        }
        parent.node_ops.unlink(parent, name);
        FS.destroyNode(node);
      },readlink:function (path) {
        var lookup = FS.lookupPath(path);
        var link = lookup.node;
        if (!link.node_ops.readlink) {
          throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
        }
        return link.node_ops.readlink(link);
      },stat:function (path, dontFollow) {
        var lookup = FS.lookupPath(path, { follow: !dontFollow });
        var node = lookup.node;
        if (!node.node_ops.getattr) {
          throw new FS.ErrnoError(ERRNO_CODES.EPERM);
        }
        return node.node_ops.getattr(node);
      },lstat:function (path) {
        return FS.stat(path, true);
      },chmod:function (path, mode, dontFollow) {
        var node;
        if (typeof path === 'string') {
          var lookup = FS.lookupPath(path, { follow: !dontFollow });
          node = lookup.node;
        } else {
          node = path;
        }
        if (!node.node_ops.setattr) {
          throw new FS.ErrnoError(ERRNO_CODES.EPERM);
        }
        node.node_ops.setattr(node, {
          mode: (mode & 4095) | (node.mode & ~4095),
          timestamp: Date.now()
        });
      },lchmod:function (path, mode) {
        FS.chmod(path, mode, true);
      },fchmod:function (fd, mode) {
        var stream = FS.getStream(fd);
        if (!stream) {
          throw new FS.ErrnoError(ERRNO_CODES.EBADF);
        }
        FS.chmod(stream.node, mode);
      },chown:function (path, uid, gid, dontFollow) {
        var node;
        if (typeof path === 'string') {
          var lookup = FS.lookupPath(path, { follow: !dontFollow });
          node = lookup.node;
        } else {
          node = path;
        }
        if (!node.node_ops.setattr) {
          throw new FS.ErrnoError(ERRNO_CODES.EPERM);
        }
        node.node_ops.setattr(node, {
          timestamp: Date.now()
          // we ignore the uid / gid for now
        });
      },lchown:function (path, uid, gid) {
        FS.chown(path, uid, gid, true);
      },fchown:function (fd, uid, gid) {
        var stream = FS.getStream(fd);
        if (!stream) {
          throw new FS.ErrnoError(ERRNO_CODES.EBADF);
        }
        FS.chown(stream.node, uid, gid);
      },truncate:function (path, len) {
        if (len < 0) {
          throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
        }
        var node;
        if (typeof path === 'string') {
          var lookup = FS.lookupPath(path, { follow: true });
          node = lookup.node;
        } else {
          node = path;
        }
        if (!node.node_ops.setattr) {
          throw new FS.ErrnoError(ERRNO_CODES.EPERM);
        }
        if (FS.isDir(node.mode)) {
          throw new FS.ErrnoError(ERRNO_CODES.EISDIR);
        }
        if (!FS.isFile(node.mode)) {
          throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
        }
        var err = FS.nodePermissions(node, 'w');
        if (err) {
          throw new FS.ErrnoError(err);
        }
        node.node_ops.setattr(node, {
          size: len,
          timestamp: Date.now()
        });
      },ftruncate:function (fd, len) {
        var stream = FS.getStream(fd);
        if (!stream) {
          throw new FS.ErrnoError(ERRNO_CODES.EBADF);
        }
        if ((stream.flags & 2097155) === 0) {
          throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
        }
        FS.truncate(stream.node, len);
      },utime:function (path, atime, mtime) {
        var lookup = FS.lookupPath(path, { follow: true });
        var node = lookup.node;
        node.node_ops.setattr(node, {
          timestamp: Math.max(atime, mtime)
        });
      },open:function (path, flags, mode, fd_start, fd_end) {
        flags = typeof flags === 'string' ? FS.modeStringToFlags(flags) : flags;
        mode = typeof mode === 'undefined' ? 438 /* 0666 */ : mode;
        if ((flags & 64)) {
          mode = (mode & 4095) | 32768;
        } else {
          mode = 0;
        }
        var node;
        if (typeof path === 'object') {
          node = path;
        } else {
          path = PATH.normalize(path);
          try {
            var lookup = FS.lookupPath(path, {
              follow: !(flags & 131072)
            });
            node = lookup.node;
          } catch (e) {
            // ignore
          }
        }
        // perhaps we need to create the node
        if ((flags & 64)) {
          if (node) {
            // if O_CREAT and O_EXCL are set, error out if the node already exists
            if ((flags & 128)) {
              throw new FS.ErrnoError(ERRNO_CODES.EEXIST);
            }
          } else {
            // node doesn't exist, try to create it
            node = FS.mknod(path, mode, 0);
          }
        }
        if (!node) {
          throw new FS.ErrnoError(ERRNO_CODES.ENOENT);
        }
        // can't truncate a device
        if (FS.isChrdev(node.mode)) {
          flags &= ~512;
        }
        // check permissions
        var err = FS.mayOpen(node, flags);
        if (err) {
          throw new FS.ErrnoError(err);
        }
        // do truncation if necessary
        if ((flags & 512)) {
          FS.truncate(node, 0);
        }
        // we've already handled these, don't pass down to the underlying vfs
        flags &= ~(128 | 512);

        // register the stream with the filesystem
        var stream = FS.createStream({
          node: node,
          path: FS.getPath(node),  // we want the absolute path to the node
          flags: flags,
          seekable: true,
          position: 0,
          stream_ops: node.stream_ops,
          // used by the file family libc calls (fopen, fwrite, ferror, etc.)
          ungotten: [],
          error: false
        }, fd_start, fd_end);
        // call the new stream's open function
        if (stream.stream_ops.open) {
          stream.stream_ops.open(stream);
        }
        if (Module['logReadFiles'] && !(flags & 1)) {
          if (!FS.readFiles) FS.readFiles = {};
          if (!(path in FS.readFiles)) {
            FS.readFiles[path] = 1;
            Module['printErr']('read file: ' + path);
          }
        }
        return stream;
      },close:function (stream) {
        try {
          if (stream.stream_ops.close) {
            stream.stream_ops.close(stream);
          }
        } catch (e) {
          throw e;
        } finally {
          FS.closeStream(stream.fd);
        }
      },llseek:function (stream, offset, whence) {
        if (!stream.seekable || !stream.stream_ops.llseek) {
          throw new FS.ErrnoError(ERRNO_CODES.ESPIPE);
        }
        return stream.stream_ops.llseek(stream, offset, whence);
      },read:function (stream, buffer, offset, length, position) {
        if (length < 0 || position < 0) {
          throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
        }
        if ((stream.flags & 2097155) === 1) {
          throw new FS.ErrnoError(ERRNO_CODES.EBADF);
        }
        if (FS.isDir(stream.node.mode)) {
          throw new FS.ErrnoError(ERRNO_CODES.EISDIR);
        }
        if (!stream.stream_ops.read) {
          throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
        }
        var seeking = true;
        if (typeof position === 'undefined') {
          position = stream.position;
          seeking = false;
        } else if (!stream.seekable) {
          throw new FS.ErrnoError(ERRNO_CODES.ESPIPE);
        }
        var bytesRead = stream.stream_ops.read(stream, buffer, offset, length, position);
        if (!seeking) stream.position += bytesRead;
        return bytesRead;
      },write:function (stream, buffer, offset, length, position, canOwn) {
        if (length < 0 || position < 0) {
          throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
        }
        if ((stream.flags & 2097155) === 0) {
          throw new FS.ErrnoError(ERRNO_CODES.EBADF);
        }
        if (FS.isDir(stream.node.mode)) {
          throw new FS.ErrnoError(ERRNO_CODES.EISDIR);
        }
        if (!stream.stream_ops.write) {
          throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
        }
        var seeking = true;
        if (typeof position === 'undefined') {
          position = stream.position;
          seeking = false;
        } else if (!stream.seekable) {
          throw new FS.ErrnoError(ERRNO_CODES.ESPIPE);
        }
        if (stream.flags & 1024) {
          // seek to the end before writing in append mode
          FS.llseek(stream, 0, 2);
        }
        var bytesWritten = stream.stream_ops.write(stream, buffer, offset, length, position, canOwn);
        if (!seeking) stream.position += bytesWritten;
        return bytesWritten;
      },allocate:function (stream, offset, length) {
        if (offset < 0 || length <= 0) {
          throw new FS.ErrnoError(ERRNO_CODES.EINVAL);
        }
        if ((stream.flags & 2097155) === 0) {
          throw new FS.ErrnoError(ERRNO_CODES.EBADF);
        }
        if (!FS.isFile(stream.node.mode) && !FS.isDir(node.mode)) {
          throw new FS.ErrnoError(ERRNO_CODES.ENODEV);
        }
        if (!stream.stream_ops.allocate) {
          throw new FS.ErrnoError(ERRNO_CODES.EOPNOTSUPP);
        }
        stream.stream_ops.allocate(stream, offset, length);
      },mmap:function (stream, buffer, offset, length, position, prot, flags) {
        // TODO if PROT is PROT_WRITE, make sure we have write access
        if ((stream.flags & 2097155) === 1) {
          throw new FS.ErrnoError(ERRNO_CODES.EACCES);
        }
        if (!stream.stream_ops.mmap) {
          throw new FS.ErrnoError(ERRNO_CODES.ENODEV);
        }
        return stream.stream_ops.mmap(stream, buffer, offset, length, position, prot, flags);
      },ioctl:function (stream, cmd, arg) {
        if (!stream.stream_ops.ioctl) {
          throw new FS.ErrnoError(ERRNO_CODES.ENOTTY);
        }
        return stream.stream_ops.ioctl(stream, cmd, arg);
      },readFile:function (path, opts) {
        opts = opts || {};
        opts.flags = opts.flags || 'r';
        opts.encoding = opts.encoding || 'binary';
        if (opts.encoding !== 'utf8' && opts.encoding !== 'binary') {
          throw new Error('Invalid encoding type "' + opts.encoding + '"');
        }
        var ret;
        var stream = FS.open(path, opts.flags);
        var stat = FS.stat(path);
        var length = stat.size;
        var buf = new Uint8Array(length);
        FS.read(stream, buf, 0, length, 0);
        if (opts.encoding === 'utf8') {
          ret = '';
          var utf8 = new Runtime.UTF8Processor();
          for (var i = 0; i < length; i++) {
            ret += utf8.processCChar(buf[i]);
          }
        } else if (opts.encoding === 'binary') {
          ret = buf;
        }
        FS.close(stream);
        return ret;
      },writeFile:function (path, data, opts) {
        opts = opts || {};
        opts.flags = opts.flags || 'w';
        opts.encoding = opts.encoding || 'utf8';
        if (opts.encoding !== 'utf8' && opts.encoding !== 'binary') {
          throw new Error('Invalid encoding type "' + opts.encoding + '"');
        }
        var stream = FS.open(path, opts.flags, opts.mode);
        if (opts.encoding === 'utf8') {
          var utf8 = new Runtime.UTF8Processor();
          var buf = new Uint8Array(utf8.processJSString(data));
          FS.write(stream, buf, 0, buf.length, 0, opts.canOwn);
        } else if (opts.encoding === 'binary') {
          FS.write(stream, data, 0, data.length, 0, opts.canOwn);
        }
        FS.close(stream);
      },cwd:function () {
        return FS.currentPath;
      },chdir:function (path) {
        var lookup = FS.lookupPath(path, { follow: true });
        if (!FS.isDir(lookup.node.mode)) {
          throw new FS.ErrnoError(ERRNO_CODES.ENOTDIR);
        }
        var err = FS.nodePermissions(lookup.node, 'x');
        if (err) {
          throw new FS.ErrnoError(err);
        }
        FS.currentPath = lookup.path;
      },createDefaultDirectories:function () {
        FS.mkdir('/tmp');
      },createDefaultDevices:function () {
        // create /dev
        FS.mkdir('/dev');
        // setup /dev/null
        FS.registerDevice(FS.makedev(1, 3), {
          read: function() { return 0; },
          write: function() { return 0; }
        });
        FS.mkdev('/dev/null', FS.makedev(1, 3));
        // setup /dev/tty and /dev/tty1
        // stderr needs to print output using Module['printErr']
        // so we register a second tty just for it.
        TTY.register(FS.makedev(5, 0), TTY.default_tty_ops);
        TTY.register(FS.makedev(6, 0), TTY.default_tty1_ops);
        FS.mkdev('/dev/tty', FS.makedev(5, 0));
        FS.mkdev('/dev/tty1', FS.makedev(6, 0));
        // we're not going to emulate the actual shm device,
        // just create the tmp dirs that reside in it commonly
        FS.mkdir('/dev/shm');
        FS.mkdir('/dev/shm/tmp');
      },createStandardStreams:function () {
        // TODO deprecate the old functionality of a single
        // input / output callback and that utilizes FS.createDevice
        // and instead require a unique set of stream ops

        // by default, we symlink the standard streams to the
        // default tty devices. however, if the standard streams
        // have been overwritten we create a unique device for
        // them instead.
        if (Module['stdin']) {
          FS.createDevice('/dev', 'stdin', Module['stdin']);
        } else {
          FS.symlink('/dev/tty', '/dev/stdin');
        }
        if (Module['stdout']) {
          FS.createDevice('/dev', 'stdout', null, Module['stdout']);
        } else {
          FS.symlink('/dev/tty', '/dev/stdout');
        }
        if (Module['stderr']) {
          FS.createDevice('/dev', 'stderr', null, Module['stderr']);
        } else {
          FS.symlink('/dev/tty1', '/dev/stderr');
        }

        // open default streams for the stdin, stdout and stderr devices
        var stdin = FS.open('/dev/stdin', 'r');
        HEAP32[((_stdin)>>2)]=FS.getPtrForStream(stdin);
        assert(stdin.fd === 0, 'invalid handle for stdin (' + stdin.fd + ')');

        var stdout = FS.open('/dev/stdout', 'w');
        HEAP32[((_stdout)>>2)]=FS.getPtrForStream(stdout);
        assert(stdout.fd === 1, 'invalid handle for stdout (' + stdout.fd + ')');

        var stderr = FS.open('/dev/stderr', 'w');
        HEAP32[((_stderr)>>2)]=FS.getPtrForStream(stderr);
        assert(stderr.fd === 2, 'invalid handle for stderr (' + stderr.fd + ')');
      },ensureErrnoError:function () {
        if (FS.ErrnoError) return;
        FS.ErrnoError = function ErrnoError(errno) {
          this.errno = errno;
          for (var key in ERRNO_CODES) {
            if (ERRNO_CODES[key] === errno) {
              this.code = key;
              break;
            }
          }
          this.message = ERRNO_MESSAGES[errno];
        };
        FS.ErrnoError.prototype = new Error();
        FS.ErrnoError.prototype.constructor = FS.ErrnoError;
        // Some errors may happen quite a bit, to avoid overhead we reuse them (and suffer a lack of stack info)
        [ERRNO_CODES.ENOENT].forEach(function(code) {
          FS.genericErrors[code] = new FS.ErrnoError(code);
          FS.genericErrors[code].stack = '<generic error, no stack>';
        });
      },staticInit:function () {
        FS.ensureErrnoError();

        FS.nameTable = new Array(4096);

        FS.mount(MEMFS, {}, '/');

        FS.createDefaultDirectories();
        FS.createDefaultDevices();
      },init:function (input, output, error) {
        assert(!FS.init.initialized, 'FS.init was previously called. If you want to initialize later with custom parameters, remove any earlier calls (note that one is automatically added to the generated code)');
        FS.init.initialized = true;

        FS.ensureErrnoError();

        // Allow Module.stdin etc. to provide defaults, if none explicitly passed to us here
        Module['stdin'] = input || Module['stdin'];
        Module['stdout'] = output || Module['stdout'];
        Module['stderr'] = error || Module['stderr'];

        FS.createStandardStreams();
      },quit:function () {
        FS.init.initialized = false;
        for (var i = 0; i < FS.streams.length; i++) {
          var stream = FS.streams[i];
          if (!stream) {
            continue;
          }
          FS.close(stream);
        }
      },getMode:function (canRead, canWrite) {
        var mode = 0;
        if (canRead) mode |= 292 | 73;
        if (canWrite) mode |= 146;
        return mode;
      },joinPath:function (parts, forceRelative) {
        var path = PATH.join.apply(null, parts);
        if (forceRelative && path[0] == '/') path = path.substr(1);
        return path;
      },absolutePath:function (relative, base) {
        return PATH.resolve(base, relative);
      },standardizePath:function (path) {
        return PATH.normalize(path);
      },findObject:function (path, dontResolveLastLink) {
        var ret = FS.analyzePath(path, dontResolveLastLink);
        if (ret.exists) {
          return ret.object;
        } else {
          ___setErrNo(ret.error);
          return null;
        }
      },analyzePath:function (path, dontResolveLastLink) {
        // operate from within the context of the symlink's target
        try {
          var lookup = FS.lookupPath(path, { follow: !dontResolveLastLink });
          path = lookup.path;
        } catch (e) {
        }
        var ret = {
          isRoot: false, exists: false, error: 0, name: null, path: null, object: null,
          parentExists: false, parentPath: null, parentObject: null
        };
        try {
          var lookup = FS.lookupPath(path, { parent: true });
          ret.parentExists = true;
          ret.parentPath = lookup.path;
          ret.parentObject = lookup.node;
          ret.name = PATH.basename(path);
          lookup = FS.lookupPath(path, { follow: !dontResolveLastLink });
          ret.exists = true;
          ret.path = lookup.path;
          ret.object = lookup.node;
          ret.name = lookup.node.name;
          ret.isRoot = lookup.path === '/';
        } catch (e) {
          ret.error = e.errno;
        };
        return ret;
      },createFolder:function (parent, name, canRead, canWrite) {
        var path = PATH.join2(typeof parent === 'string' ? parent : FS.getPath(parent), name);
        var mode = FS.getMode(canRead, canWrite);
        return FS.mkdir(path, mode);
      },createPath:function (parent, path, canRead, canWrite) {
        parent = typeof parent === 'string' ? parent : FS.getPath(parent);
        var parts = path.split('/').reverse();
        while (parts.length) {
          var part = parts.pop();
          if (!part) continue;
          var current = PATH.join2(parent, part);
          try {
            FS.mkdir(current);
          } catch (e) {
            // ignore EEXIST
          }
          parent = current;
        }
        return current;
      },createFile:function (parent, name, properties, canRead, canWrite) {
        var path = PATH.join2(typeof parent === 'string' ? parent : FS.getPath(parent), name);
        var mode = FS.getMode(canRead, canWrite);
        return FS.create(path, mode);
      },createDataFile:function (parent, name, data, canRead, canWrite, canOwn) {
        var path = name ? PATH.join2(typeof parent === 'string' ? parent : FS.getPath(parent), name) : parent;
        var mode = FS.getMode(canRead, canWrite);
        var node = FS.create(path, mode);
        if (data) {
          if (typeof data === 'string') {
            var arr = new Array(data.length);
            for (var i = 0, len = data.length; i < len; ++i) arr[i] = data.charCodeAt(i);
            data = arr;
          }
          // make sure we can write to the file
          FS.chmod(node, mode | 146);
          var stream = FS.open(node, 'w');
          FS.write(stream, data, 0, data.length, 0, canOwn);
          FS.close(stream);
          FS.chmod(node, mode);
        }
        return node;
      },createDevice:function (parent, name, input, output) {
        var path = PATH.join2(typeof parent === 'string' ? parent : FS.getPath(parent), name);
        var mode = FS.getMode(!!input, !!output);
        if (!FS.createDevice.major) FS.createDevice.major = 64;
        var dev = FS.makedev(FS.createDevice.major++, 0);
        // Create a fake device that a set of stream ops to emulate
        // the old behavior.
        FS.registerDevice(dev, {
          open: function(stream) {
            stream.seekable = false;
          },
          close: function(stream) {
            // flush any pending line data
            if (output && output.buffer && output.buffer.length) {
              output(10);
            }
          },
          read: function(stream, buffer, offset, length, pos /* ignored */) {
            var bytesRead = 0;
            for (var i = 0; i < length; i++) {
              var result;
              try {
                result = input();
              } catch (e) {
                throw new FS.ErrnoError(ERRNO_CODES.EIO);
              }
              if (result === undefined && bytesRead === 0) {
                throw new FS.ErrnoError(ERRNO_CODES.EAGAIN);
              }
              if (result === null || result === undefined) break;
              bytesRead++;
              buffer[offset+i] = result;
            }
            if (bytesRead) {
              stream.node.timestamp = Date.now();
            }
            return bytesRead;
          },
          write: function(stream, buffer, offset, length, pos) {
            for (var i = 0; i < length; i++) {
              try {
                output(buffer[offset+i]);
              } catch (e) {
                throw new FS.ErrnoError(ERRNO_CODES.EIO);
              }
            }
            if (length) {
              stream.node.timestamp = Date.now();
            }
            return i;
          }
        });
        return FS.mkdev(path, mode, dev);
      },createLink:function (parent, name, target, canRead, canWrite) {
        var path = PATH.join2(typeof parent === 'string' ? parent : FS.getPath(parent), name);
        return FS.symlink(target, path);
      },forceLoadFile:function (obj) {
        if (obj.isDevice || obj.isFolder || obj.link || obj.contents) return true;
        var success = true;
        if (typeof XMLHttpRequest !== 'undefined') {
          throw new Error("Lazy loading should have been performed (contents set) in createLazyFile, but it was not. Lazy loading only works in web workers. Use --embed-file or --preload-file in emcc on the main thread.");
        } else if (Module['read']) {
          // Command-line.
          try {
            // WARNING: Can't read binary files in V8's d8 or tracemonkey's js, as
            //          read() will try to parse UTF8.
            obj.contents = intArrayFromString(Module['read'](obj.url), true);
          } catch (e) {
            success = false;
          }
        } else {
          throw new Error('Cannot load without read() or XMLHttpRequest.');
        }
        if (!success) ___setErrNo(ERRNO_CODES.EIO);
        return success;
      },createLazyFile:function (parent, name, url, canRead, canWrite) {
        // Lazy chunked Uint8Array (implements get and length from Uint8Array). Actual getting is abstracted away for eventual reuse.
        function LazyUint8Array() {
          this.lengthKnown = false;
          this.chunks = []; // Loaded chunks. Index is the chunk number
        }
        LazyUint8Array.prototype.get = function LazyUint8Array_get(idx) {
          if (idx > this.length-1 || idx < 0) {
            return undefined;
          }
          var chunkOffset = idx % this.chunkSize;
          var chunkNum = Math.floor(idx / this.chunkSize);
          return this.getter(chunkNum)[chunkOffset];
        }
        LazyUint8Array.prototype.setDataGetter = function LazyUint8Array_setDataGetter(getter) {
          this.getter = getter;
        }
        LazyUint8Array.prototype.cacheLength = function LazyUint8Array_cacheLength() {
            // Find length
            var xhr = new XMLHttpRequest();
            xhr.open('HEAD', url, false);
            xhr.send(null);
            if (!(xhr.status >= 200 && xhr.status < 300 || xhr.status === 304)) throw new Error("Couldn't load " + url + ". Status: " + xhr.status);
            var datalength = Number(xhr.getResponseHeader("Content-length"));
            var header;
            var hasByteServing = (header = xhr.getResponseHeader("Accept-Ranges")) && header === "bytes";
            var chunkSize = 1024*1024; // Chunk size in bytes

            if (!hasByteServing) chunkSize = datalength;

            // Function to get a range from the remote URL.
            var doXHR = (function(from, to) {
              if (from > to) throw new Error("invalid range (" + from + ", " + to + ") or no bytes requested!");
              if (to > datalength-1) throw new Error("only " + datalength + " bytes available! programmer error!");

              // TODO: Use mozResponseArrayBuffer, responseStream, etc. if available.
              var xhr = new XMLHttpRequest();
              xhr.open('GET', url, false);
              if (datalength !== chunkSize) xhr.setRequestHeader("Range", "bytes=" + from + "-" + to);

              // Some hints to the browser that we want binary data.
              if (typeof Uint8Array != 'undefined') xhr.responseType = 'arraybuffer';
              if (xhr.overrideMimeType) {
                xhr.overrideMimeType('text/plain; charset=x-user-defined');
              }

              xhr.send(null);
              if (!(xhr.status >= 200 && xhr.status < 300 || xhr.status === 304)) throw new Error("Couldn't load " + url + ". Status: " + xhr.status);
              if (xhr.response !== undefined) {
                return new Uint8Array(xhr.response || []);
              } else {
                return intArrayFromString(xhr.responseText || '', true);
              }
            });
            var lazyArray = this;
            lazyArray.setDataGetter(function(chunkNum) {
              var start = chunkNum * chunkSize;
              var end = (chunkNum+1) * chunkSize - 1; // including this byte
              end = Math.min(end, datalength-1); // if datalength-1 is selected, this is the last block
              if (typeof(lazyArray.chunks[chunkNum]) === "undefined") {
                lazyArray.chunks[chunkNum] = doXHR(start, end);
              }
              if (typeof(lazyArray.chunks[chunkNum]) === "undefined") throw new Error("doXHR failed!");
              return lazyArray.chunks[chunkNum];
            });

            this._length = datalength;
            this._chunkSize = chunkSize;
            this.lengthKnown = true;
        }
        if (typeof XMLHttpRequest !== 'undefined') {
          if (!ENVIRONMENT_IS_WORKER) throw 'Cannot do synchronous binary XHRs outside webworkers in modern browsers. Use --embed-file or --preload-file in emcc';
          var lazyArray = new LazyUint8Array();
          Object.defineProperty(lazyArray, "length", {
              get: function() {
                  if(!this.lengthKnown) {
                      this.cacheLength();
                  }
                  return this._length;
              }
          });
          Object.defineProperty(lazyArray, "chunkSize", {
              get: function() {
                  if(!this.lengthKnown) {
                      this.cacheLength();
                  }
                  return this._chunkSize;
              }
          });

          var properties = { isDevice: false, contents: lazyArray };
        } else {
          var properties = { isDevice: false, url: url };
        }

        var node = FS.createFile(parent, name, properties, canRead, canWrite);
        // This is a total hack, but I want to get this lazy file code out of the
        // core of MEMFS. If we want to keep this lazy file concept I feel it should
        // be its own thin LAZYFS proxying calls to MEMFS.
        if (properties.contents) {
          node.contents = properties.contents;
        } else if (properties.url) {
          node.contents = null;
          node.url = properties.url;
        }
        // override each stream op with one that tries to force load the lazy file first
        var stream_ops = {};
        var keys = Object.keys(node.stream_ops);
        keys.forEach(function(key) {
          var fn = node.stream_ops[key];
          stream_ops[key] = function forceLoadLazyFile() {
            if (!FS.forceLoadFile(node)) {
              throw new FS.ErrnoError(ERRNO_CODES.EIO);
            }
            return fn.apply(null, arguments);
          };
        });
        // use a custom read function
        stream_ops.read = function stream_ops_read(stream, buffer, offset, length, position) {
          if (!FS.forceLoadFile(node)) {
            throw new FS.ErrnoError(ERRNO_CODES.EIO);
          }
          var contents = stream.node.contents;
          if (position >= contents.length)
            return 0;
          var size = Math.min(contents.length - position, length);
          assert(size >= 0);
          if (contents.slice) { // normal array
            for (var i = 0; i < size; i++) {
              buffer[offset + i] = contents[position + i];
            }
          } else {
            for (var i = 0; i < size; i++) { // LazyUint8Array from sync binary XHR
              buffer[offset + i] = contents.get(position + i);
            }
          }
          return size;
        };
        node.stream_ops = stream_ops;
        return node;
      },createPreloadedFile:function (parent, name, url, canRead, canWrite, onload, onerror, dontCreateFile, canOwn) {
        Browser.init();
        // TODO we should allow people to just pass in a complete filename instead
        // of parent and name being that we just join them anyways
        var fullname = name ? PATH.resolve(PATH.join2(parent, name)) : parent;
        function processData(byteArray) {
          function finish(byteArray) {
            if (!dontCreateFile) {
              FS.createDataFile(parent, name, byteArray, canRead, canWrite, canOwn);
            }
            if (onload) onload();
            removeRunDependency('cp ' + fullname);
          }
          var handled = false;
          Module['preloadPlugins'].forEach(function(plugin) {
            if (handled) return;
            if (plugin['canHandle'](fullname)) {
              plugin['handle'](byteArray, fullname, finish, function() {
                if (onerror) onerror();
                removeRunDependency('cp ' + fullname);
              });
              handled = true;
            }
          });
          if (!handled) finish(byteArray);
        }
        addRunDependency('cp ' + fullname);
        if (typeof url == 'string') {
          Browser.asyncLoad(url, function(byteArray) {
            processData(byteArray);
          }, onerror);
        } else {
          processData(url);
        }
      },indexedDB:function () {
        return window.indexedDB || window.mozIndexedDB || window.webkitIndexedDB || window.msIndexedDB;
      },DB_NAME:function () {
        return 'EM_FS_' + window.location.pathname;
      },DB_VERSION:20,DB_STORE_NAME:"FILE_DATA",saveFilesToDB:function (paths, onload, onerror) {
        onload = onload || function(){};
        onerror = onerror || function(){};
        var indexedDB = FS.indexedDB();
        try {
          var openRequest = indexedDB.open(FS.DB_NAME(), FS.DB_VERSION);
        } catch (e) {
          return onerror(e);
        }
        openRequest.onupgradeneeded = function openRequest_onupgradeneeded() {
          console.log('creating db');
          var db = openRequest.result;
          db.createObjectStore(FS.DB_STORE_NAME);
        };
        openRequest.onsuccess = function openRequest_onsuccess() {
          var db = openRequest.result;
          var transaction = db.transaction([FS.DB_STORE_NAME], 'readwrite');
          var files = transaction.objectStore(FS.DB_STORE_NAME);
          var ok = 0, fail = 0, total = paths.length;
          function finish() {
            if (fail == 0) onload(); else onerror();
          }
          paths.forEach(function(path) {
            var putRequest = files.put(FS.analyzePath(path).object.contents, path);
            putRequest.onsuccess = function putRequest_onsuccess() { ok++; if (ok + fail == total) finish() };
            putRequest.onerror = function putRequest_onerror() { fail++; if (ok + fail == total) finish() };
          });
          transaction.onerror = onerror;
        };
        openRequest.onerror = onerror;
      },loadFilesFromDB:function (paths, onload, onerror) {
        onload = onload || function(){};
        onerror = onerror || function(){};
        var indexedDB = FS.indexedDB();
        try {
          var openRequest = indexedDB.open(FS.DB_NAME(), FS.DB_VERSION);
        } catch (e) {
          return onerror(e);
        }
        openRequest.onupgradeneeded = onerror; // no database to load from
        openRequest.onsuccess = function openRequest_onsuccess() {
          var db = openRequest.result;
          try {
            var transaction = db.transaction([FS.DB_STORE_NAME], 'readonly');
          } catch(e) {
            onerror(e);
            return;
          }
          var files = transaction.objectStore(FS.DB_STORE_NAME);
          var ok = 0, fail = 0, total = paths.length;
          function finish() {
            if (fail == 0) onload(); else onerror();
          }
          paths.forEach(function(path) {
            var getRequest = files.get(path);
            getRequest.onsuccess = function getRequest_onsuccess() {
              if (FS.analyzePath(path).exists) {
                FS.unlink(path);
              }
              FS.createDataFile(PATH.dirname(path), PATH.basename(path), getRequest.result, true, true, true);
              ok++;
              if (ok + fail == total) finish();
            };
            getRequest.onerror = function getRequest_onerror() { fail++; if (ok + fail == total) finish() };
          });
          transaction.onerror = onerror;
        };
        openRequest.onerror = onerror;
      }};var PATH={splitPath:function (filename) {
        var splitPathRe = /^(\/?|)([\s\S]*?)((?:\.{1,2}|[^\/]+?|)(\.[^.\/]*|))(?:[\/]*)$/;
        return splitPathRe.exec(filename).slice(1);
      },normalizeArray:function (parts, allowAboveRoot) {
        // if the path tries to go above the root, `up` ends up > 0
        var up = 0;
        for (var i = parts.length - 1; i >= 0; i--) {
          var last = parts[i];
          if (last === '.') {
            parts.splice(i, 1);
          } else if (last === '..') {
            parts.splice(i, 1);
            up++;
          } else if (up) {
            parts.splice(i, 1);
            up--;
          }
        }
        // if the path is allowed to go above the root, restore leading ..s
        if (allowAboveRoot) {
          for (; up--; up) {
            parts.unshift('..');
          }
        }
        return parts;
      },normalize:function (path) {
        var isAbsolute = path.charAt(0) === '/',
            trailingSlash = path.substr(-1) === '/';
        // Normalize the path
        path = PATH.normalizeArray(path.split('/').filter(function(p) {
          return !!p;
        }), !isAbsolute).join('/');
        if (!path && !isAbsolute) {
          path = '.';
        }
        if (path && trailingSlash) {
          path += '/';
        }
        return (isAbsolute ? '/' : '') + path;
      },dirname:function (path) {
        var result = PATH.splitPath(path),
            root = result[0],
            dir = result[1];
        if (!root && !dir) {
          // No dirname whatsoever
          return '.';
        }
        if (dir) {
          // It has a dirname, strip trailing slash
          dir = dir.substr(0, dir.length - 1);
        }
        return root + dir;
      },basename:function (path) {
        // EMSCRIPTEN return '/'' for '/', not an empty string
        if (path === '/') return '/';
        var lastSlash = path.lastIndexOf('/');
        if (lastSlash === -1) return path;
        return path.substr(lastSlash+1);
      },extname:function (path) {
        return PATH.splitPath(path)[3];
      },join:function () {
        var paths = Array.prototype.slice.call(arguments, 0);
        return PATH.normalize(paths.join('/'));
      },join2:function (l, r) {
        return PATH.normalize(l + '/' + r);
      },resolve:function () {
        var resolvedPath = '',
          resolvedAbsolute = false;
        for (var i = arguments.length - 1; i >= -1 && !resolvedAbsolute; i--) {
          var path = (i >= 0) ? arguments[i] : FS.cwd();
          // Skip empty and invalid entries
          if (typeof path !== 'string') {
            throw new TypeError('Arguments to path.resolve must be strings');
          } else if (!path) {
            continue;
          }
          resolvedPath = path + '/' + resolvedPath;
          resolvedAbsolute = path.charAt(0) === '/';
        }
        // At this point the path should be resolved to a full absolute path, but
        // handle relative paths to be safe (might happen when process.cwd() fails)
        resolvedPath = PATH.normalizeArray(resolvedPath.split('/').filter(function(p) {
          return !!p;
        }), !resolvedAbsolute).join('/');
        return ((resolvedAbsolute ? '/' : '') + resolvedPath) || '.';
      },relative:function (from, to) {
        from = PATH.resolve(from).substr(1);
        to = PATH.resolve(to).substr(1);
        function trim(arr) {
          var start = 0;
          for (; start < arr.length; start++) {
            if (arr[start] !== '') break;
          }
          var end = arr.length - 1;
          for (; end >= 0; end--) {
            if (arr[end] !== '') break;
          }
          if (start > end) return [];
          return arr.slice(start, end - start + 1);
        }
        var fromParts = trim(from.split('/'));
        var toParts = trim(to.split('/'));
        var length = Math.min(fromParts.length, toParts.length);
        var samePartsLength = length;
        for (var i = 0; i < length; i++) {
          if (fromParts[i] !== toParts[i]) {
            samePartsLength = i;
            break;
          }
        }
        var outputParts = [];
        for (var i = samePartsLength; i < fromParts.length; i++) {
          outputParts.push('..');
        }
        outputParts = outputParts.concat(toParts.slice(samePartsLength));
        return outputParts.join('/');
      }};var Browser={mainLoop:{scheduler:null,method:"",shouldPause:false,paused:false,queue:[],pause:function () {
          Browser.mainLoop.shouldPause = true;
        },resume:function () {
          if (Browser.mainLoop.paused) {
            Browser.mainLoop.paused = false;
            Browser.mainLoop.scheduler();
          }
          Browser.mainLoop.shouldPause = false;
        },updateStatus:function () {
          if (Module['setStatus']) {
            var message = Module['statusMessage'] || 'Please wait...';
            var remaining = Browser.mainLoop.remainingBlockers;
            var expected = Browser.mainLoop.expectedBlockers;
            if (remaining) {
              if (remaining < expected) {
                Module['setStatus'](message + ' (' + (expected - remaining) + '/' + expected + ')');
              } else {
                Module['setStatus'](message);
              }
            } else {
              Module['setStatus']('');
            }
          }
        }},isFullScreen:false,pointerLock:false,moduleContextCreatedCallbacks:[],workers:[],init:function () {
        if (!Module["preloadPlugins"]) Module["preloadPlugins"] = []; // needs to exist even in workers

        if (Browser.initted || ENVIRONMENT_IS_WORKER) return;
        Browser.initted = true;

        try {
          new Blob();
          Browser.hasBlobConstructor = true;
        } catch(e) {
          Browser.hasBlobConstructor = false;
          console.log("warning: no blob constructor, cannot create blobs with mimetypes");
        }
        Browser.BlobBuilder = typeof MozBlobBuilder != "undefined" ? MozBlobBuilder : (typeof WebKitBlobBuilder != "undefined" ? WebKitBlobBuilder : (!Browser.hasBlobConstructor ? console.log("warning: no BlobBuilder") : null));
        Browser.URLObject = typeof window != "undefined" ? (window.URL ? window.URL : window.webkitURL) : undefined;
        if (!Module.noImageDecoding && typeof Browser.URLObject === 'undefined') {
          console.log("warning: Browser does not support creating object URLs. Built-in browser image decoding will not be available.");
          Module.noImageDecoding = true;
        }

        // Support for plugins that can process preloaded files. You can add more of these to
        // your app by creating and appending to Module.preloadPlugins.
        //
        // Each plugin is asked if it can handle a file based on the file's name. If it can,
        // it is given the file's raw data. When it is done, it calls a callback with the file's
        // (possibly modified) data. For example, a plugin might decompress a file, or it
        // might create some side data structure for use later (like an Image element, etc.).

        var imagePlugin = {};
        imagePlugin['canHandle'] = function imagePlugin_canHandle(name) {
          return !Module.noImageDecoding && /\.(jpg|jpeg|png|bmp)$/i.test(name);
        };
        imagePlugin['handle'] = function imagePlugin_handle(byteArray, name, onload, onerror) {
          var b = null;
          if (Browser.hasBlobConstructor) {
            try {
              b = new Blob([byteArray], { type: Browser.getMimetype(name) });
              if (b.size !== byteArray.length) { // Safari bug #118630
                // Safari's Blob can only take an ArrayBuffer
                b = new Blob([(new Uint8Array(byteArray)).buffer], { type: Browser.getMimetype(name) });
              }
            } catch(e) {
              Runtime.warnOnce('Blob constructor present but fails: ' + e + '; falling back to blob builder');
            }
          }
          if (!b) {
            var bb = new Browser.BlobBuilder();
            bb.append((new Uint8Array(byteArray)).buffer); // we need to pass a buffer, and must copy the array to get the right data range
            b = bb.getBlob();
          }
          var url = Browser.URLObject.createObjectURL(b);
          var img = new Image();
          img.onload = function img_onload() {
            assert(img.complete, 'Image ' + name + ' could not be decoded');
            var canvas = document.createElement('canvas');
            canvas.width = img.width;
            canvas.height = img.height;
            var ctx = canvas.getContext('2d');
            ctx.drawImage(img, 0, 0);
            Module["preloadedImages"][name] = canvas;
            Browser.URLObject.revokeObjectURL(url);
            if (onload) onload(byteArray);
          };
          img.onerror = function img_onerror(event) {
            console.log('Image ' + url + ' could not be decoded');
            if (onerror) onerror();
          };
          img.src = url;
        };
        Module['preloadPlugins'].push(imagePlugin);

        var audioPlugin = {};
        audioPlugin['canHandle'] = function audioPlugin_canHandle(name) {
          return !Module.noAudioDecoding && name.substr(-4) in { '.ogg': 1, '.wav': 1, '.mp3': 1 };
        };
        audioPlugin['handle'] = function audioPlugin_handle(byteArray, name, onload, onerror) {
          var done = false;
          function finish(audio) {
            if (done) return;
            done = true;
            Module["preloadedAudios"][name] = audio;
            if (onload) onload(byteArray);
          }
          function fail() {
            if (done) return;
            done = true;
            Module["preloadedAudios"][name] = new Audio(); // empty shim
            if (onerror) onerror();
          }
          if (Browser.hasBlobConstructor) {
            try {
              var b = new Blob([byteArray], { type: Browser.getMimetype(name) });
            } catch(e) {
              return fail();
            }
            var url = Browser.URLObject.createObjectURL(b); // XXX we never revoke this!
            var audio = new Audio();
            audio.addEventListener('canplaythrough', function() { finish(audio) }, false); // use addEventListener due to chromium bug 124926
            audio.onerror = function audio_onerror(event) {
              if (done) return;
              console.log('warning: browser could not fully decode audio ' + name + ', trying slower base64 approach');
              function encode64(data) {
                var BASE = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';
                var PAD = '=';
                var ret = '';
                var leftchar = 0;
                var leftbits = 0;
                for (var i = 0; i < data.length; i++) {
                  leftchar = (leftchar << 8) | data[i];
                  leftbits += 8;
                  while (leftbits >= 6) {
                    var curr = (leftchar >> (leftbits-6)) & 0x3f;
                    leftbits -= 6;
                    ret += BASE[curr];
                  }
                }
                if (leftbits == 2) {
                  ret += BASE[(leftchar&3) << 4];
                  ret += PAD + PAD;
                } else if (leftbits == 4) {
                  ret += BASE[(leftchar&0xf) << 2];
                  ret += PAD;
                }
                return ret;
              }
              audio.src = 'data:audio/x-' + name.substr(-3) + ';base64,' + encode64(byteArray);
              finish(audio); // we don't wait for confirmation this worked - but it's worth trying
            };
            audio.src = url;
            // workaround for chrome bug 124926 - we do not always get oncanplaythrough or onerror
            Browser.safeSetTimeout(function() {
              finish(audio); // try to use it even though it is not necessarily ready to play
            }, 10000);
          } else {
            return fail();
          }
        };
        Module['preloadPlugins'].push(audioPlugin);

        // Canvas event setup

        var canvas = Module['canvas'];

        // forced aspect ratio can be enabled by defining 'forcedAspectRatio' on Module
        // Module['forcedAspectRatio'] = 4 / 3;

        canvas.requestPointerLock = canvas['requestPointerLock'] ||
                                    canvas['mozRequestPointerLock'] ||
                                    canvas['webkitRequestPointerLock'] ||
                                    canvas['msRequestPointerLock'] ||
                                    function(){};
        canvas.exitPointerLock = document['exitPointerLock'] ||
                                 document['mozExitPointerLock'] ||
                                 document['webkitExitPointerLock'] ||
                                 document['msExitPointerLock'] ||
                                 function(){}; // no-op if function does not exist
        canvas.exitPointerLock = canvas.exitPointerLock.bind(document);

        function pointerLockChange() {
          Browser.pointerLock = document['pointerLockElement'] === canvas ||
                                document['mozPointerLockElement'] === canvas ||
                                document['webkitPointerLockElement'] === canvas ||
                                document['msPointerLockElement'] === canvas;
        }

        document.addEventListener('pointerlockchange', pointerLockChange, false);
        document.addEventListener('mozpointerlockchange', pointerLockChange, false);
        document.addEventListener('webkitpointerlockchange', pointerLockChange, false);
        document.addEventListener('mspointerlockchange', pointerLockChange, false);

        if (Module['elementPointerLock']) {
          canvas.addEventListener("click", function(ev) {
            if (!Browser.pointerLock && canvas.requestPointerLock) {
              canvas.requestPointerLock();
              ev.preventDefault();
            }
          }, false);
        }
      },createContext:function (canvas, useWebGL, setInModule, webGLContextAttributes) {
        var ctx;
        var errorInfo = '?';
        function onContextCreationError(event) {
          errorInfo = event.statusMessage || errorInfo;
        }
        try {
          if (useWebGL) {
            var contextAttributes = {
              antialias: false,
              alpha: false
            };

            if (webGLContextAttributes) {
              for (var attribute in webGLContextAttributes) {
                contextAttributes[attribute] = webGLContextAttributes[attribute];
              }
            }


            canvas.addEventListener('webglcontextcreationerror', onContextCreationError, false);
            try {
              ['experimental-webgl', 'webgl'].some(function(webglId) {
                return ctx = canvas.getContext(webglId, contextAttributes);
              });
            } finally {
              canvas.removeEventListener('webglcontextcreationerror', onContextCreationError, false);
            }
          } else {
            ctx = canvas.getContext('2d');
          }
          if (!ctx) throw ':(';
        } catch (e) {
          Module.print('Could not create canvas: ' + [errorInfo, e]);
          return null;
        }
        if (useWebGL) {
          // Set the background of the WebGL canvas to black
          canvas.style.backgroundColor = "white";

          // Warn on context loss
          canvas.addEventListener('webglcontextlost', function(event) {
            alert('WebGL context lost. You will need to reload the page.');
          }, false);
        }
        if (setInModule) {
          GLctx = Module.ctx = ctx;
          Module.useWebGL = useWebGL;
          Browser.moduleContextCreatedCallbacks.forEach(function(callback) { callback() });
          Browser.init();
        }
        return ctx;
      },destroyContext:function (canvas, useWebGL, setInModule) {},fullScreenHandlersInstalled:false,lockPointer:undefined,resizeCanvas:undefined,requestFullScreen:function (lockPointer, resizeCanvas) {
        Browser.lockPointer = lockPointer;
        Browser.resizeCanvas = resizeCanvas;
        if (typeof Browser.lockPointer === 'undefined') Browser.lockPointer = true;
        if (typeof Browser.resizeCanvas === 'undefined') Browser.resizeCanvas = false;

        var canvas = Module['canvas'];
        function fullScreenChange() {
          Browser.isFullScreen = false;
          var canvasContainer = canvas.parentNode;
          if ((document['webkitFullScreenElement'] || document['webkitFullscreenElement'] ||
               document['mozFullScreenElement'] || document['mozFullscreenElement'] ||
               document['fullScreenElement'] || document['fullscreenElement'] ||
               document['msFullScreenElement'] || document['msFullscreenElement'] ||
               document['webkitCurrentFullScreenElement']) === canvasContainer) {
            canvas.cancelFullScreen = document['cancelFullScreen'] ||
                                      document['mozCancelFullScreen'] ||
                                      document['webkitCancelFullScreen'] ||
                                      document['msExitFullscreen'] ||
                                      document['exitFullscreen'] ||
                                      function() {};
            canvas.cancelFullScreen = canvas.cancelFullScreen.bind(document);
            if (Browser.lockPointer) canvas.requestPointerLock();
            Browser.isFullScreen = true;
            if (Browser.resizeCanvas) Browser.setFullScreenCanvasSize();
          } else {

            // remove the full screen specific parent of the canvas again to restore the HTML structure from before going full screen
            canvasContainer.parentNode.insertBefore(canvas, canvasContainer);
            canvasContainer.parentNode.removeChild(canvasContainer);

            if (Browser.resizeCanvas) Browser.setWindowedCanvasSize();
          }
          if (Module['onFullScreen']) Module['onFullScreen'](Browser.isFullScreen);
          Browser.updateCanvasDimensions(canvas);
        }

        if (!Browser.fullScreenHandlersInstalled) {
          Browser.fullScreenHandlersInstalled = true;
          document.addEventListener('fullscreenchange', fullScreenChange, false);
          document.addEventListener('mozfullscreenchange', fullScreenChange, false);
          document.addEventListener('webkitfullscreenchange', fullScreenChange, false);
          document.addEventListener('MSFullscreenChange', fullScreenChange, false);
        }

        // create a new parent to ensure the canvas has no siblings. this allows browsers to optimize full screen performance when its parent is the full screen root
        var canvasContainer = document.createElement("div");
        canvas.parentNode.insertBefore(canvasContainer, canvas);
        canvasContainer.appendChild(canvas);

        // use parent of canvas as full screen root to allow aspect ratio correction (Firefox stretches the root to screen size)
        canvasContainer.requestFullScreen = canvasContainer['requestFullScreen'] ||
                                            canvasContainer['mozRequestFullScreen'] ||
                                            canvasContainer['msRequestFullscreen'] ||
                                           (canvasContainer['webkitRequestFullScreen'] ? function() { canvasContainer['webkitRequestFullScreen'](Element['ALLOW_KEYBOARD_INPUT']) } : null);
        canvasContainer.requestFullScreen();
      },requestAnimationFrame:function requestAnimationFrame(func) {
        if (typeof window === 'undefined') { // Provide fallback to setTimeout if window is undefined (e.g. in Node.js)
          setTimeout(func, 1000/60);
        } else {
          if (!window.requestAnimationFrame) {
            window.requestAnimationFrame = window['requestAnimationFrame'] ||
                                           window['mozRequestAnimationFrame'] ||
                                           window['webkitRequestAnimationFrame'] ||
                                           window['msRequestAnimationFrame'] ||
                                           window['oRequestAnimationFrame'] ||
                                           window['setTimeout'];
          }
          window.requestAnimationFrame(func);
        }
      },safeCallback:function (func) {
        return function() {
          if (!ABORT) return func.apply(null, arguments);
        };
      },safeRequestAnimationFrame:function (func) {
        return Browser.requestAnimationFrame(function() {
          if (!ABORT) func();
        });
      },safeSetTimeout:function (func, timeout) {
        return setTimeout(function() {
          if (!ABORT) func();
        }, timeout);
      },safeSetInterval:function (func, timeout) {
        return setInterval(function() {
          if (!ABORT) func();
        }, timeout);
      },getMimetype:function (name) {
        return {
          'jpg': 'image/jpeg',
          'jpeg': 'image/jpeg',
          'png': 'image/png',
          'bmp': 'image/bmp',
          'ogg': 'audio/ogg',
          'wav': 'audio/wav',
          'mp3': 'audio/mpeg'
        }[name.substr(name.lastIndexOf('.')+1)];
      },getUserMedia:function (func) {
        if(!window.getUserMedia) {
          window.getUserMedia = navigator['getUserMedia'] ||
                                navigator['mozGetUserMedia'];
        }
        window.getUserMedia(func);
      },getMovementX:function (event) {
        return event['movementX'] ||
               event['mozMovementX'] ||
               event['webkitMovementX'] ||
               0;
      },getMovementY:function (event) {
        return event['movementY'] ||
               event['mozMovementY'] ||
               event['webkitMovementY'] ||
               0;
      },getMouseWheelDelta:function (event) {
        return Math.max(-1, Math.min(1, event.type === 'DOMMouseScroll' ? event.detail : -event.wheelDelta));
      },mouseX:0,mouseY:0,mouseMovementX:0,mouseMovementY:0,touches:{},lastTouches:{},calculateMouseEvent:function (event) { // event should be mousemove, mousedown or mouseup
        if (Browser.pointerLock) {
          // When the pointer is locked, calculate the coordinates
          // based on the movement of the mouse.
          // Workaround for Firefox bug 764498
          if (event.type != 'mousemove' &&
              ('mozMovementX' in event)) {
            Browser.mouseMovementX = Browser.mouseMovementY = 0;
          } else {
            Browser.mouseMovementX = Browser.getMovementX(event);
            Browser.mouseMovementY = Browser.getMovementY(event);
          }

          // check if SDL is available
          if (typeof SDL != "undefined") {
          	Browser.mouseX = SDL.mouseX + Browser.mouseMovementX;
          	Browser.mouseY = SDL.mouseY + Browser.mouseMovementY;
          } else {
          	// just add the mouse delta to the current absolut mouse position
          	// FIXME: ideally this should be clamped against the canvas size and zero
          	Browser.mouseX += Browser.mouseMovementX;
          	Browser.mouseY += Browser.mouseMovementY;
          }
        } else {
          // Otherwise, calculate the movement based on the changes
          // in the coordinates.
          var rect = Module["canvas"].getBoundingClientRect();
          var cw = Module["canvas"].width;
          var ch = Module["canvas"].height;

          // Neither .scrollX or .pageXOffset are defined in a spec, but
          // we prefer .scrollX because it is currently in a spec draft.
          // (see: http://www.w3.org/TR/2013/WD-cssom-view-20131217/)
          var scrollX = ((typeof window.scrollX !== 'undefined') ? window.scrollX : window.pageXOffset);
          var scrollY = ((typeof window.scrollY !== 'undefined') ? window.scrollY : window.pageYOffset);

          if (event.type === 'touchstart' || event.type === 'touchend' || event.type === 'touchmove') {
            var touch = event.touch;
            if (touch === undefined) {
              return; // the "touch" property is only defined in SDL

            }
            var adjustedX = touch.pageX - (scrollX + rect.left);
            var adjustedY = touch.pageY - (scrollY + rect.top);

            adjustedX = adjustedX * (cw / rect.width);
            adjustedY = adjustedY * (ch / rect.height);

            var coords = { x: adjustedX, y: adjustedY };

            if (event.type === 'touchstart') {
              Browser.lastTouches[touch.identifier] = coords;
              Browser.touches[touch.identifier] = coords;
            } else if (event.type === 'touchend' || event.type === 'touchmove') {
              Browser.lastTouches[touch.identifier] = Browser.touches[touch.identifier];
              Browser.touches[touch.identifier] = { x: adjustedX, y: adjustedY };
            }
            return;
          }

          var x = event.pageX - (scrollX + rect.left);
          var y = event.pageY - (scrollY + rect.top);

          // the canvas might be CSS-scaled compared to its backbuffer;
          // SDL-using content will want mouse coordinates in terms
          // of backbuffer units.
          x = x * (cw / rect.width);
          y = y * (ch / rect.height);

          Browser.mouseMovementX = x - Browser.mouseX;
          Browser.mouseMovementY = y - Browser.mouseY;
          Browser.mouseX = x;
          Browser.mouseY = y;
        }
      },xhrLoad:function (url, onload, onerror) {
        var xhr = new XMLHttpRequest();
        xhr.open('GET', url, true);
        xhr.responseType = 'arraybuffer';
        xhr.onload = function xhr_onload() {
          if (xhr.status == 200 || (xhr.status == 0 && xhr.response)) { // file URLs can return 0
            onload(xhr.response);
          } else {
            onerror();
          }
        };
        xhr.onerror = onerror;
        xhr.send(null);
      },asyncLoad:function (url, onload, onerror, noRunDep) {
        Browser.xhrLoad(url, function(arrayBuffer) {
          assert(arrayBuffer, 'Loading data file "' + url + '" failed (no arrayBuffer).');
          onload(new Uint8Array(arrayBuffer));
          if (!noRunDep) removeRunDependency('al ' + url);
        }, function(event) {
          if (onerror) {
            onerror();
          } else {
            throw 'Loading data file "' + url + '" failed.';
          }
        });
        if (!noRunDep) addRunDependency('al ' + url);
      },resizeListeners:[],updateResizeListeners:function () {
        var canvas = Module['canvas'];
        Browser.resizeListeners.forEach(function(listener) {
          listener(canvas.width, canvas.height);
        });
      },setCanvasSize:function (width, height, noUpdates) {
        var canvas = Module['canvas'];
        Browser.updateCanvasDimensions(canvas, width, height);
        if (!noUpdates) Browser.updateResizeListeners();
      },windowedWidth:0,windowedHeight:0,setFullScreenCanvasSize:function () {
        // check if SDL is available
        if (typeof SDL != "undefined") {
        	var flags = HEAPU32[((SDL.screen+Runtime.QUANTUM_SIZE*0)>>2)];
        	flags = flags | 0x00800000; // set SDL_FULLSCREEN flag
        	HEAP32[((SDL.screen+Runtime.QUANTUM_SIZE*0)>>2)]=flags
        }
        Browser.updateResizeListeners();
      },setWindowedCanvasSize:function () {
        // check if SDL is available
        if (typeof SDL != "undefined") {
        	var flags = HEAPU32[((SDL.screen+Runtime.QUANTUM_SIZE*0)>>2)];
        	flags = flags & ~0x00800000; // clear SDL_FULLSCREEN flag
        	HEAP32[((SDL.screen+Runtime.QUANTUM_SIZE*0)>>2)]=flags
        }
        Browser.updateResizeListeners();
      },updateCanvasDimensions:function (canvas, wNative, hNative) {
        if (wNative && hNative) {
          canvas.widthNative = wNative;
          canvas.heightNative = hNative;
        } else {
          wNative = canvas.widthNative;
          hNative = canvas.heightNative;
        }
        var w = wNative;
        var h = hNative;
        if (Module['forcedAspectRatio'] && Module['forcedAspectRatio'] > 0) {
          if (w/h < Module['forcedAspectRatio']) {
            w = Math.round(h * Module['forcedAspectRatio']);
          } else {
            h = Math.round(w / Module['forcedAspectRatio']);
          }
        }
        if (((document['webkitFullScreenElement'] || document['webkitFullscreenElement'] ||
             document['mozFullScreenElement'] || document['mozFullscreenElement'] ||
             document['fullScreenElement'] || document['fullscreenElement'] ||
             document['msFullScreenElement'] || document['msFullscreenElement'] ||
             document['webkitCurrentFullScreenElement']) === canvas.parentNode) && (typeof screen != 'undefined')) {
           var factor = Math.min(screen.width / w, screen.height / h);
           w = Math.round(w * factor);
           h = Math.round(h * factor);
        }
        if (Browser.resizeCanvas) {
          if (canvas.width  != w) canvas.width  = w;
          if (canvas.height != h) canvas.height = h;
          if (typeof canvas.style != 'undefined') {
            canvas.style.removeProperty( "width");
            canvas.style.removeProperty("height");
          }
        } else {
          if (canvas.width  != wNative) canvas.width  = wNative;
          if (canvas.height != hNative) canvas.height = hNative;
          if (typeof canvas.style != 'undefined') {
            if (w != wNative || h != hNative) {
              canvas.style.setProperty( "width", w + "px", "important");
              canvas.style.setProperty("height", h + "px", "important");
            } else {
              canvas.style.removeProperty( "width");
              canvas.style.removeProperty("height");
            }
          }
        }
      }};

  function _sprintf(s, format, varargs) {
      // int sprintf(char *restrict s, const char *restrict format, ...);
      // http://pubs.opengroup.org/onlinepubs/000095399/functions/printf.html
      return _snprintf(s, undefined, format, varargs);
    }

  function _js_dialog_string(index, title, initialtext) {
          dlg_form.appendChild(document.createTextNode(Pointer_stringify(title)));
          var editbox = document.createElement("input");
          editbox.type = "text";
          editbox.value = Pointer_stringify(initialtext);
          dlg_form.appendChild(editbox);
          dlg_form.appendChild(document.createElement("br"));

          dlg_return_funcs.push(function() {
              dlg_return_sval(index, editbox.value);
          });
      }

  function _js_canvas_clip_rect(x, y, w, h) {
          ctx.save();
          ctx.beginPath();
          ctx.rect(x, y, w, h);
          ctx.clip();
      }

  function _js_canvas_make_statusbar() {
          var statusholder = document.getElementById("statusbarholder");
          statusbar = document.createElement("div");
          statusbar.style.overflow = "hidden";
          statusbar.style.width = (onscreen_canvas.width - 4) + "px";
          statusholder.style.width = onscreen_canvas.width + "px";
          statusbar.style.height = "1.2em";
          statusbar.style.textAlign = "left";
          //statusbar.style.background = "#d8d8d8";
          //statusbar.style.borderLeft = '2px solid #c8c8c8';
          //statusbar.style.borderTop = '2px solid #c8c8c8';
          //statusbar.style.borderRight = '2px solid #e8e8e8';
          //statusbar.style.borderBottom = '2px solid #e8e8e8';
          statusbar.appendChild(document.createTextNode(" "));
          statusholder.appendChild(statusbar);
      }

  function _js_dialog_init(titletext) {
          // Create an overlay on the page which darkens everything
          // beneath it.
          dlg_dimmer = document.createElement("div");
          dlg_dimmer.style.width = "100%";
          dlg_dimmer.style.height = "100%";
          //dlg_dimmer.style.background = '#000000';
          //dlg_dimmer.style.position = 'fixed';
          //dlg_dimmer.style.opacity = 0.3;
          dlg_dimmer.style.top = dlg_dimmer.style.left = 0;
          dlg_dimmer.style["z-index"] = 99;

          // Now create a form which sits on top of that in turn.
          dlg_form = document.createElement("form");
          dlg_form.style.width = (window.innerWidth * 2 / 3) + "px";
          //dlg_form.style.opacity = 1;
          //dlg_form.style.background = '#ffffff';
          //dlg_form.style.color = '#000000';
          dlg_form.style.position = 'absolute';
          //dlg_form.style.border = "2px solid black";
          dlg_form.style.padding = "20px";
          dlg_form.style.top = (window.innerHeight / 10) + "px";
          dlg_form.style.left = (window.innerWidth / 6) + "px";
          dlg_form.style["z-index"] = 100;

          var title = document.createElement("p");
          title.style.marginTop = "0px";
          title.appendChild(document.createTextNode
                            (Pointer_stringify(titletext)));
          dlg_form.appendChild(title);

          dlg_return_funcs = [];
          dlg_next_id = 0;
      }

  function _sysconf(name) {
      // long sysconf(int name);
      // http://pubs.opengroup.org/onlinepubs/009695399/functions/sysconf.html
      switch(name) {
        case 30: return PAGE_SIZE;
        case 132:
        case 133:
        case 12:
        case 137:
        case 138:
        case 15:
        case 235:
        case 16:
        case 17:
        case 18:
        case 19:
        case 20:
        case 149:
        case 13:
        case 10:
        case 236:
        case 153:
        case 9:
        case 21:
        case 22:
        case 159:
        case 154:
        case 14:
        case 77:
        case 78:
        case 139:
        case 80:
        case 81:
        case 79:
        case 82:
        case 68:
        case 67:
        case 164:
        case 11:
        case 29:
        case 47:
        case 48:
        case 95:
        case 52:
        case 51:
        case 46:
          return 200809;
        case 27:
        case 246:
        case 127:
        case 128:
        case 23:
        case 24:
        case 160:
        case 161:
        case 181:
        case 182:
        case 242:
        case 183:
        case 184:
        case 243:
        case 244:
        case 245:
        case 165:
        case 178:
        case 179:
        case 49:
        case 50:
        case 168:
        case 169:
        case 175:
        case 170:
        case 171:
        case 172:
        case 97:
        case 76:
        case 32:
        case 173:
        case 35:
          return -1;
        case 176:
        case 177:
        case 7:
        case 155:
        case 8:
        case 157:
        case 125:
        case 126:
        case 92:
        case 93:
        case 129:
        case 130:
        case 131:
        case 94:
        case 91:
          return 1;
        case 74:
        case 60:
        case 69:
        case 70:
        case 4:
          return 1024;
        case 31:
        case 42:
        case 72:
          return 32;
        case 87:
        case 26:
        case 33:
          return 2147483647;
        case 34:
        case 1:
          return 47839;
        case 38:
        case 36:
          return 99;
        case 43:
        case 37:
          return 2048;
        case 0: return 2097152;
        case 3: return 65536;
        case 28: return 32768;
        case 44: return 32767;
        case 75: return 16384;
        case 39: return 1000;
        case 89: return 700;
        case 71: return 256;
        case 40: return 255;
        case 2: return 100;
        case 180: return 64;
        case 25: return 20;
        case 5: return 16;
        case 6: return 6;
        case 73: return 4;
        case 84: return 1;
      }
      ___setErrNo(ERRNO_CODES.EINVAL);
      return -1;
    }

  function _js_dialog_launch() {
          // Put in the OK and Cancel buttons at the bottom.
          var button;

          button = document.createElement("input");
          button.type = "button";
          button.value = "OK";
          button.onclick = function(event) {
              for (var i in dlg_return_funcs)
                  dlg_return_funcs[i]();
              command(3);
          }
          dlg_form.appendChild(button);

          button = document.createElement("input");
          button.type = "button";
          button.value = "Cancel";
          button.onclick = function(event) {
              command(4);
          }
          dlg_form.appendChild(button);

          document.body.appendChild(dlg_dimmer);
          document.body.appendChild(dlg_form);
      }

  function _js_activate_timer() {
          if (timer === null) {
              timer_reference_date = (new Date()).valueOf();
              timer = setInterval(function() {
                  var now = (new Date()).valueOf();
                  timer_callback((now - timer_reference_date) / 1000.0);
                  timer_reference_date = now;
                  return true;
              }, 20);
          }
      }





  var _environ=allocate(1, "i32*", ALLOC_STATIC);var ___environ=_environ;function ___buildEnvironment(env) {
      // WARNING: Arbitrary limit!
      var MAX_ENV_VALUES = 64;
      var TOTAL_ENV_SIZE = 1024;

      // Statically allocate memory for the environment.
      var poolPtr;
      var envPtr;
      if (!___buildEnvironment.called) {
        ___buildEnvironment.called = true;
        // Set default values. Use string keys for Closure Compiler compatibility.
        ENV['USER'] = 'root';
        ENV['PATH'] = '/';
        ENV['PWD'] = '/';
        ENV['HOME'] = '/home/emscripten';
        ENV['LANG'] = 'en_US.UTF-8';
        ENV['_'] = './this.program';
        // Allocate memory.
        poolPtr = allocate(TOTAL_ENV_SIZE, 'i8', ALLOC_STATIC);
        envPtr = allocate(MAX_ENV_VALUES * 4,
                          'i8*', ALLOC_STATIC);
        HEAP32[((envPtr)>>2)]=poolPtr;
        HEAP32[((_environ)>>2)]=envPtr;
      } else {
        envPtr = HEAP32[((_environ)>>2)];
        poolPtr = HEAP32[((envPtr)>>2)];
      }

      // Collect key=value lines.
      var strings = [];
      var totalSize = 0;
      for (var key in env) {
        if (typeof env[key] === 'string') {
          var line = key + '=' + env[key];
          strings.push(line);
          totalSize += line.length;
        }
      }
      if (totalSize > TOTAL_ENV_SIZE) {
        throw new Error('Environment size exceeded TOTAL_ENV_SIZE!');
      }

      // Make new.
      var ptrSize = 4;
      for (var i = 0; i < strings.length; i++) {
        var line = strings[i];
        writeAsciiToMemory(line, poolPtr);
        HEAP32[(((envPtr)+(i * ptrSize))>>2)]=poolPtr;
        poolPtr += line.length + 1;
      }
      HEAP32[(((envPtr)+(strings.length * ptrSize))>>2)]=0;
    }var ENV={};function _getenv(name) {
      // char *getenv(const char *name);
      // http://pubs.opengroup.org/onlinepubs/009695399/functions/getenv.html
      if (name === 0) return 0;
      name = Pointer_stringify(name);
      if (!ENV.hasOwnProperty(name)) return 0;

      if (_getenv.ret) _free(_getenv.ret);
      _getenv.ret = allocate(intArrayFromString(ENV[name]), 'i8', ALLOC_NORMAL);
      return _getenv.ret;
    }

  function _js_remove_solve_button() {
          document.getElementById("solve").style.display = "none";
      }

  function _js_remove_type_dropdown() {
          document.getElementById("gametype").style.display = "none";
      }

  function _js_get_selected_preset() {
          for (var i in gametypeoptions) {
              if (gametypeoptions[i].selected) {
                  return gametypeoptions[i].value;
              }
          }
          return 0;
      }

  function _js_canvas_draw_text(x, y, halign, colptr, fontptr, text) {
          ctx.font = Pointer_stringify(fontptr);
          ctx.fillStyle = Pointer_stringify(colptr);
          ctx.textAlign = (halign == 0 ? 'left' :
                           halign == 1 ? 'center' : 'right');
          ctx.textBaseline = 'alphabetic';
          ctx.fillText(Pointer_stringify(text), x, y);
      }

  function _js_canvas_draw_rect(x, y, w, h, colptr) {
          ctx.fillStyle = "#ffffff"; //Pointer_stringify(colptr);
          ctx.fillRect(x, y, w, h);
      }

  var _ceil=Math_ceil;

  function _js_add_preset(ptr) {
          var name = (ptr == 0 ? "Customise..." : Pointer_stringify(ptr));
          var value = gametypeoptions.length;

          var option = document.createElement("option");
          option.value = value;
          option.appendChild(document.createTextNode(name));
          gametypeselector.appendChild(option);
          gametypeoptions.push(option);

          if (ptr == 0) {
              // The option we've just created is the one for inventing
              // a new custom setup.
              gametypenewcustom = option;
              option.value = -1;

              // Now create another element called 'Custom', which will
              // be auto-selected by us to indicate the custom settings
              // you've previously selected. However, we don't add it to
              // the game type selector; it will only appear when the
              // user actually has custom settings selected.
              option = document.createElement("option");
              option.value = -2;
              option.appendChild(document.createTextNode("Custom"));
              gametypethiscustom = option;
          }
      }

  function _js_canvas_draw_line(x1, y1, x2, y2, width, colour) {
          colour = Pointer_stringify(colour);

          ctx.beginPath();
          ctx.moveTo(x1 + 0.5, y1 + 0.5);
          ctx.lineTo(x2 + 0.5, y2 + 0.5);
          ctx.lineWidth = width;
          ctx.lineCap = 'round';
          ctx.lineJoin = 'round';
          //ctx.strokeStyle = colour;
          //ctx.stroke();
          ctx.fillStyle = colour;
          ctx.fillRect(x1, y1, 1, 1);
          ctx.fillRect(x2, y2, 1, 1);
      }

  function _js_canvas_copy_to_blitter(id, x, y, w, h) {
          var blitter_ctx = blitters[id].getContext('2d');
          blitter_ctx.drawImage(offscreen_canvas,
                                x, y, w, h,
                                0, 0, w, h);
      }

  function _js_canvas_unclip() {
          ctx.restore();
      }

  function _js_enable_undo_redo(undo, redo) {
          undo_button.disabled = (undo == 0);
          redo_button.disabled = (redo == 0);
      }

  function _sbrk(bytes) {
      // Implement a Linux-like 'memory area' for our 'process'.
      // Changes the size of the memory area by |bytes|; returns the
      // address of the previous top ('break') of the memory area
      // We control the "dynamic" memory - DYNAMIC_BASE to DYNAMICTOP
      var self = _sbrk;
      if (!self.called) {
        DYNAMICTOP = alignMemoryPage(DYNAMICTOP); // make sure we start out aligned
        self.called = true;
        assert(Runtime.dynamicAlloc);
        self.alloc = Runtime.dynamicAlloc;
        Runtime.dynamicAlloc = function() { abort('cannot dynamically allocate, sbrk now has control') };
      }
      var ret = DYNAMICTOP;
      if (bytes != 0) self.alloc(bytes);
      return ret;  // Previous break location.
    }

  function _js_canvas_draw_poly(pointptr, npoints, fill, outline) {
          ctx.beginPath();
          ctx.moveTo(getValue(pointptr  , 'i32') + 0.5,
                     getValue(pointptr+4, 'i32') + 0.5);
          for (var i = 1; i < npoints; i++)
              ctx.lineTo(getValue(pointptr+8*i  , 'i32') + 0.5,
                         getValue(pointptr+8*i+4, 'i32') + 0.5);
          ctx.closePath();
          if (fill != 0) {
              ctx.fillStyle = Pointer_stringify(fill);
              ctx.fill();
          }
          ctx.lineWidth = '1';
          ctx.lineCap = 'round';
          ctx.lineJoin = 'round';
          ctx.strokeStyle = Pointer_stringify(outline);
          ctx.stroke();
      }

  function ___errno_location() {
      return ___errno_state;
    }

  function _js_canvas_find_font_midpoint(height, font) {
          font = Pointer_stringify(font);

          // Reuse cached value if possible
          if (midpoint_cache[font] !== undefined)
              return midpoint_cache[font];

          // Find the width of the string
          var ctx1 = onscreen_canvas.getContext('2d');
          ctx1.font = font;
          var width = (ctx1.measureText(midpoint_test_str).width + 1) | 0;

          // Construct a test canvas of appropriate size, initialise it to
          // black, and draw the string on it in white
          var measure_canvas = document.createElement('canvas');
          var ctx2 = measure_canvas.getContext('2d');
          ctx2.canvas.width = width;
          ctx2.canvas.height = 2*height;
          //ctx2.fillStyle = "#000000";
          ctx2.fillRect(0, 0, width, 2*height);
          var baseline = (1.5*height) | 0;
          //ctx2.fillStyle = "#ffffff";
          ctx2.font = font;
          ctx2.fillText(midpoint_test_str, 0, baseline);

          // Scan the contents of the test canvas to find the top and bottom
          // set pixels.
          var pixels = ctx2.getImageData(0, 0, width, 2*height).data;
          var ymin = 2*height, ymax = -1;
          for (var y = 0; y < 2*height; y++) {
              for (var x = 0; x < width; x++) {
                  if (pixels[4*(y*width+x)] != 0) {
                      if (ymin > y) ymin = y;
                      if (ymax < y) ymax = y;
                      break;
                  }
              }
          }

          var ret = (baseline - (ymin + ymax) / 2) | 0;
          midpoint_cache[font] = ret;
          return ret;
      }

  function _js_canvas_set_statusbar(ptr) {
          var text = Pointer_stringify(ptr);
          statusbar.replaceChild(document.createTextNode(text),
                                 statusbar.lastChild);
      }

  function _isspace(chr) {
      return (chr == 32) || (chr >= 9 && chr <= 13);
    }

  function _js_error_box(ptr) {
          alert(Pointer_stringify(ptr));
      }

  function _js_canvas_set_size(w, h) {
          onscreen_canvas.width = w;
          offscreen_canvas.width = w;
          if (statusbar !== null) {
              statusbar.style.width = (w - 4) + "px";
              document.getElementById("statusbarholder").style.width = w + "px";
          }
          //resizable_div.style.width = w + "px";

          onscreen_canvas.height = h;
          offscreen_canvas.height = h;
      }

  function _js_canvas_free_blitter(id) {
          blitters[id] = null;
      }


  Module["_strcpy"] = _strcpy;

  function _js_select_preset(n) {
          if (gametypethiscustom !== null) {
              // Fiddle with the Custom/Customise options. If we're
              // about to select the Custom option, then it should be in
              // the menu, and the other one should read "Re-customise";
              // if we're about to select another one, then the static
              // Custom option should disappear and the other one should
              // read "Customise".

              if (gametypethiscustom.parentNode == gametypeselector)
                  gametypeselector.removeChild(gametypethiscustom);
              if (gametypenewcustom.parentNode == gametypeselector)
                  gametypeselector.removeChild(gametypenewcustom);

              if (n < 0) {
                  gametypeselector.appendChild(gametypethiscustom);
                  gametypenewcustom.lastChild.data = "Re-customise...";
              } else {
                  gametypenewcustom.lastChild.data = "Customise...";
              }
              gametypeselector.appendChild(gametypenewcustom);
              gametypenewcustom.selected = false;
          }

          if (n < 0) {
              gametypethiscustom.selected = true;
          } else {
              gametypeoptions[n].selected = true;
          }
      }

  function _time(ptr) {
      var ret = Math.floor(Date.now()/1000);
      if (ptr) {
        HEAP32[((ptr)>>2)]=ret;
      }
      return ret;
    }

  function _js_dialog_boolean(index, title, initvalue) {
          var checkbox = document.createElement("input");
          checkbox.type = "checkbox";
          checkbox.id = "cb" + String(dlg_next_id++);
          checkbox.checked = (initvalue != 0);
          dlg_form.appendChild(checkbox);
          var checkboxlabel = document.createElement("label");
          checkboxlabel.setAttribute("for", checkbox.id);
          checkboxlabel.textContent = Pointer_stringify(title);
          dlg_form.appendChild(checkboxlabel);
          dlg_form.appendChild(document.createElement("br"));

          dlg_return_funcs.push(function() {
              dlg_return_ival(index, checkbox.checked ? 1 : 0);
          });
      }

  function _js_dialog_choices(index, title, choicelist, initvalue) {
          dlg_form.appendChild(document.createTextNode(Pointer_stringify(title)));
          var dropdown = document.createElement("select");
          var choicestr = Pointer_stringify(choicelist);
          var items = choicestr.slice(1).split(choicestr[0]);
          var options = [];
          for (var i in items) {
              var option = document.createElement("option");
              option.value = i;
              option.appendChild(document.createTextNode(items[i]));
              if (i == initvalue) option.selected = true;
              dropdown.appendChild(option);
              options.push(option);
          }
          dlg_form.appendChild(dropdown);
          dlg_form.appendChild(document.createElement("br"));

          dlg_return_funcs.push(function() {
              var val = 0;
              for (var i in options) {
                  if (options[i].selected) {
                      val = options[i].value;
                      break;
                  }
              }
              dlg_return_ival(index, val);
          });
      }
Module["requestFullScreen"] = function Module_requestFullScreen(lockPointer, resizeCanvas) { Browser.requestFullScreen(lockPointer, resizeCanvas) };
  Module["requestAnimationFrame"] = function Module_requestAnimationFrame(func) { Browser.requestAnimationFrame(func) };
  Module["setCanvasSize"] = function Module_setCanvasSize(width, height, noUpdates) { Browser.setCanvasSize(width, height, noUpdates) };
  Module["pauseMainLoop"] = function Module_pauseMainLoop() { Browser.mainLoop.pause() };
  Module["resumeMainLoop"] = function Module_resumeMainLoop() { Browser.mainLoop.resume() };
  Module["getUserMedia"] = function Module_getUserMedia() { Browser.getUserMedia() }
FS.staticInit();__ATINIT__.unshift({ func: function() { if (!Module["noFSInit"] && !FS.init.initialized) FS.init() } });__ATMAIN__.push({ func: function() { FS.ignorePermissions = false } });__ATEXIT__.push({ func: function() { FS.quit() } });Module["FS_createFolder"] = FS.createFolder;Module["FS_createPath"] = FS.createPath;Module["FS_createDataFile"] = FS.createDataFile;Module["FS_createPreloadedFile"] = FS.createPreloadedFile;Module["FS_createLazyFile"] = FS.createLazyFile;Module["FS_createLink"] = FS.createLink;Module["FS_createDevice"] = FS.createDevice;
___errno_state = Runtime.staticAlloc(4); HEAP32[((___errno_state)>>2)]=0;
__ATINIT__.unshift({ func: function() { TTY.init() } });__ATEXIT__.push({ func: function() { TTY.shutdown() } });TTY.utf8 = new Runtime.UTF8Processor();
if (ENVIRONMENT_IS_NODE) { var fs = require("fs"); NODEFS.staticInit(); }
___buildEnvironment(ENV);
STACK_BASE = STACKTOP = Runtime.alignMemory(STATICTOP);

staticSealed = true; // seal the static portion of memory

STACK_MAX = STACK_BASE + 5242880;

DYNAMIC_BASE = DYNAMICTOP = Runtime.alignMemory(STACK_MAX);

assert(DYNAMIC_BASE < TOTAL_MEMORY, "TOTAL_MEMORY not big enough for stack");


var Math_min = Math.min;
function invoke_iiiii(index,a1,a2,a3,a4) {
  try {
    return Module["dynCall_iiiii"](index,a1,a2,a3,a4);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_viiiii(index,a1,a2,a3,a4,a5) {
  try {
    Module["dynCall_viiiii"](index,a1,a2,a3,a4,a5);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_i(index) {
  try {
    return Module["dynCall_i"](index);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_vi(index,a1) {
  try {
    Module["dynCall_vi"](index,a1);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_vii(index,a1,a2) {
  try {
    Module["dynCall_vii"](index,a1,a2);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_iiiiiii(index,a1,a2,a3,a4,a5,a6) {
  try {
    return Module["dynCall_iiiiiii"](index,a1,a2,a3,a4,a5,a6);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_vidddddi(index,a1,a2,a3,a4,a5,a6,a7) {
  try {
    Module["dynCall_vidddddi"](index,a1,a2,a3,a4,a5,a6,a7);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_viiiiiidd(index,a1,a2,a3,a4,a5,a6,a7,a8) {
  try {
    Module["dynCall_viiiiiidd"](index,a1,a2,a3,a4,a5,a6,a7,a8);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_ii(index,a1) {
  try {
    return Module["dynCall_ii"](index,a1);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_iiii(index,a1,a2,a3) {
  try {
    return Module["dynCall_iiii"](index,a1,a2,a3);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_viii(index,a1,a2,a3) {
  try {
    Module["dynCall_viii"](index,a1,a2,a3);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_viiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8) {
  try {
    Module["dynCall_viiiiiiii"](index,a1,a2,a3,a4,a5,a6,a7,a8);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_viiiiii(index,a1,a2,a3,a4,a5,a6) {
  try {
    Module["dynCall_viiiiii"](index,a1,a2,a3,a4,a5,a6);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_iii(index,a1,a2) {
  try {
    return Module["dynCall_iii"](index,a1,a2);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_diiii(index,a1,a2,a3,a4) {
  try {
    return Module["dynCall_diiii"](index,a1,a2,a3,a4);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function invoke_viiii(index,a1,a2,a3,a4) {
  try {
    Module["dynCall_viiii"](index,a1,a2,a3,a4);
  } catch(e) {
    if (typeof e !== 'number' && e !== 'longjmp') throw e;
    asm["setThrew"](1, 0);
  }
}

function asmPrintInt(x, y) {
  Module.print('int ' + x + ',' + y);// + ' ' + new Error().stack);
}
function asmPrintFloat(x, y) {
  Module.print('float ' + x + ',' + y);// + ' ' + new Error().stack);
}
// EMSCRIPTEN_START_ASM
var asm=(function(global,env,buffer){"use asm";var a=new global.Int8Array(buffer);var b=new global.Int16Array(buffer);var c=new global.Int32Array(buffer);var d=new global.Uint8Array(buffer);var e=new global.Uint16Array(buffer);var f=new global.Uint32Array(buffer);var g=new global.Float32Array(buffer);var h=new global.Float64Array(buffer);var i=env.STACKTOP|0;var j=env.STACK_MAX|0;var k=env.tempDoublePtr|0;var l=env.ABORT|0;var m=0;var n=0;var o=0;var p=0;var q=+env.NaN,r=+env.Infinity;var s=0,t=0,u=0,v=0,w=0.0,x=0,y=0,z=0,A=0.0;var B=0;var C=0;var D=0;var E=0;var F=0;var G=0;var H=0;var I=0;var J=0;var K=0;var L=global.Math.floor;var M=global.Math.abs;var N=global.Math.sqrt;var O=global.Math.pow;var P=global.Math.cos;var Q=global.Math.sin;var R=global.Math.tan;var S=global.Math.acos;var T=global.Math.asin;var U=global.Math.atan;var V=global.Math.atan2;var W=global.Math.exp;var X=global.Math.log;var Y=global.Math.ceil;var Z=global.Math.imul;var _=env.abort;var $=env.assert;var aa=env.asmPrintInt;var ba=env.asmPrintFloat;var ca=env.min;var da=env.invoke_iiiii;var ea=env.invoke_viiiii;var fa=env.invoke_i;var ga=env.invoke_vi;var ha=env.invoke_vii;var ia=env.invoke_iiiiiii;var ja=env.invoke_vidddddi;var ka=env.invoke_viiiiiidd;var la=env.invoke_ii;var ma=env.invoke_iiii;var na=env.invoke_viii;var oa=env.invoke_viiiiiiii;var pa=env.invoke_viiiiii;var qa=env.invoke_iii;var ra=env.invoke_diiii;var sa=env.invoke_viiii;var ta=env._fabs;var ua=env._js_error_box;var va=env._js_dialog_cleanup;var wa=env._js_select_preset;var xa=env._js_dialog_init;var ya=env._js_canvas_draw_line;var za=env.__reallyNegative;var Aa=env._ceil;var Ba=env._js_canvas_find_font_midpoint;var Ca=env.___assert_fail;var Da=env.___buildEnvironment;var Ea=env._js_focus_canvas;var Fa=env._js_canvas_set_size;var Ga=env._js_dialog_launch;var Ha=env._js_get_selected_preset;var Ia=env._js_canvas_draw_circle;var Ja=env._js_canvas_draw_rect;var Ka=env._sscanf;var La=env._sbrk;var Ma=env._js_dialog_boolean;var Na=env._js_canvas_new_blitter;var Oa=env._snprintf;var Pa=env.___errno_location;var Qa=env._emscripten_memcpy_big;var Ra=env._js_canvas_make_statusbar;var Sa=env._js_remove_type_dropdown;var Ta=env._sysconf;var Ua=env._js_canvas_unclip;var Va=env.___setErrNo;var Wa=env._js_canvas_draw_text;var Xa=env._js_dialog_string;var Ya=env._floor;var Za=env._js_canvas_draw_update;var _a=env._js_update_permalinks;var $a=env._isspace;var ab=env._js_remove_solve_button;var bb=env._getenv;var cb=env._sprintf;var db=env._js_canvas_start_draw;var eb=env._js_enable_undo_redo;var fb=env._toupper;var gb=env._js_get_date_64;var hb=env._fflush;var ib=env.__scanString;var jb=env._js_deactivate_timer;var kb=env._vsnprintf;var lb=env._js_canvas_copy_from_blitter;var mb=env._js_activate_timer;var nb=env._js_canvas_end_draw;var ob=env.__getFloat;var pb=env._abort;var qb=env._js_dialog_choices;var rb=env._js_canvas_copy_to_blitter;var sb=env._time;var tb=env._isdigit;var ub=env._js_canvas_set_statusbar;var vb=env._abs;var wb=env.__formatString;var xb=env._js_canvas_clip_rect;var yb=env._sqrt;var zb=env._js_canvas_draw_poly;var Ab=env._js_canvas_free_blitter;var Bb=env._js_add_preset;var Cb=0.0;
// EMSCRIPTEN_START_FUNCS
function Oe(b){b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0;d=i;i=i+96|0;e=d+80|0;f=d+76|0;g=d+72|0;h=d+68|0;j=d+64|0;k=d+60|0;l=d+56|0;m=d+52|0;n=d+48|0;o=d+44|0;p=d+40|0;q=d+36|0;r=d+32|0;s=d+28|0;t=d+24|0;u=d+20|0;v=d+16|0;w=d+12|0;x=d+8|0;y=d+4|0;z=d;c[e>>2]=b;c[p>>2]=c[c[e>>2]>>2];if((c[(c[e>>2]|0)+24>>2]|0)!=0){Ca(2344,2368,957,2376)}c[q>>2]=c[(c[p>>2]|0)+4>>2];if((c[c[q>>2]>>2]|0)!=4){Ca(2400,2368,961,2376)}c[n>>2]=M((c[(c[c[(c[q>>2]|0)+8>>2]>>2]|0)+12>>2]|0)-(c[(c[(c[(c[q>>2]|0)+8>>2]|0)+8>>2]|0)+12>>2]|0)|0)|0;c[f>>2]=((c[(c[p>>2]|0)+32>>2]|0)-(c[(c[p>>2]|0)+24>>2]|0)|0)/(c[n>>2]|0)|0;c[g>>2]=((c[(c[p>>2]|0)+36>>2]|0)-(c[(c[p>>2]|0)+28>>2]|0)|0)/(c[n>>2]|0)|0;c[h>>2]=(c[f>>2]<<1)+2;c[j>>2]=(c[g>>2]<<1)+1;c[o>>2]=_f((Z(c[h>>2]|0,c[j>>2]|0)|0)+1|0)|0;c[l>>2]=0;while(1){if((c[l>>2]|0)>=(c[j>>2]|0)){break}c[k>>2]=0;while(1){A=Z(c[l>>2]|0,c[h>>2]|0)|0;if((c[k>>2]|0)>=((c[h>>2]|0)-1|0)){break}a[(c[o>>2]|0)+(A+(c[k>>2]|0))|0]=32;c[k>>2]=(c[k>>2]|0)+1}a[(c[o>>2]|0)+(A+(c[h>>2]|0)-1)|0]=10;c[l>>2]=(c[l>>2]|0)+1}A=Z(c[j>>2]|0,c[h>>2]|0)|0;a[(c[o>>2]|0)+A|0]=0;c[m>>2]=0;while(1){if((c[m>>2]|0)>=(c[(c[p>>2]|0)+8>>2]|0)){break}c[r>>2]=(c[(c[p>>2]|0)+12>>2]|0)+(c[m>>2]<<4);c[s>>2]=((c[(c[c[r>>2]>>2]|0)+12>>2]|0)-(c[(c[p>>2]|0)+24>>2]|0)|0)/(c[n>>2]|0)|0;c[t>>2]=((c[(c[(c[r>>2]|0)+4>>2]|0)+12>>2]|0)-(c[(c[p>>2]|0)+24>>2]|0)|0)/(c[n>>2]|0)|0;c[u>>2]=((c[(c[c[r>>2]>>2]|0)+16>>2]|0)-(c[(c[p>>2]|0)+28>>2]|0)|0)/(c[n>>2]|0)|0;c[v>>2]=((c[(c[(c[r>>2]|0)+4>>2]|0)+16>>2]|0)-(c[(c[p>>2]|0)+28>>2]|0)|0)/(c[n>>2]|0)|0;c[k>>2]=(c[s>>2]|0)+(c[t>>2]|0);c[l>>2]=(c[u>>2]|0)+(c[v>>2]|0);A=a[(c[(c[e>>2]|0)+8>>2]|0)+(c[m>>2]|0)|0]|0;if((A|0)==2){j=Z(c[l>>2]|0,c[h>>2]|0)|0;a[(c[o>>2]|0)+(j+(c[k>>2]|0))|0]=120}else if((A|0)==0){j=Z(c[l>>2]|0,c[h>>2]|0)|0;a[(c[o>>2]|0)+(j+(c[k>>2]|0))|0]=(c[u>>2]|0)==(c[v>>2]|0)?45:124}else if((A|0)!=1){B=16;break}c[m>>2]=(c[m>>2]|0)+1}if((B|0)==16){Ca(2416,2368,1003,2376)}c[m>>2]=0;while(1){if((c[m>>2]|0)>=(c[c[p>>2]>>2]|0)){B=27;break}c[q>>2]=(c[(c[p>>2]|0)+4>>2]|0)+((c[m>>2]|0)*24|0);if((c[c[q>>2]>>2]|0)!=4){B=21;break}c[w>>2]=((c[(c[c[(c[q>>2]|0)+8>>2]>>2]|0)+12>>2]|0)-(c[(c[p>>2]|0)+24>>2]|0)|0)/(c[n>>2]|0)|0;c[x>>2]=((c[(c[(c[(c[q>>2]|0)+8>>2]|0)+8>>2]|0)+12>>2]|0)-(c[(c[p>>2]|0)+24>>2]|0)|0)/(c[n>>2]|0)|0;c[y>>2]=((c[(c[c[(c[q>>2]|0)+8>>2]>>2]|0)+16>>2]|0)-(c[(c[p>>2]|0)+28>>2]|0)|0)/(c[n>>2]|0)|0;c[z>>2]=((c[(c[(c[(c[q>>2]|0)+8>>2]|0)+8>>2]|0)+16>>2]|0)-(c[(c[p>>2]|0)+28>>2]|0)|0)/(c[n>>2]|0)|0;c[k>>2]=(c[w>>2]|0)+(c[x>>2]|0);c[l>>2]=(c[y>>2]|0)+(c[z>>2]|0);do{if((a[(c[(c[e>>2]|0)+4>>2]|0)+(c[m>>2]|0)|0]|0)>=0){v=a[(c[(c[e>>2]|0)+4>>2]|0)+(c[m>>2]|0)|0]|0;if((a[(c[(c[e>>2]|0)+4>>2]|0)+(c[m>>2]|0)|0]|0)<10){C=v+48|0;break}else{C=v-10+65|0;break}}else{C=32}}while(0);v=Z(c[l>>2]|0,c[h>>2]|0)|0;a[(c[o>>2]|0)+(v+(c[k>>2]|0))|0]=C;c[m>>2]=(c[m>>2]|0)+1}if((B|0)==21){Ca(2400,2368,1012,2376)}else if((B|0)==27){i=d;return c[o>>2]|0}return 0}function Pe(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;i=b;return 0}function Qe(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;i=b;return}function Re(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;i=b;return 0}function Se(a,b){a=a|0;b=b|0;var d=0;d=i;i=i+16|0;c[d+4>>2]=a;c[d>>2]=b;i=d;return}function Te(a,b,d){a=a|0;b=b|0;d=d|0;var e=0;e=i;i=i+16|0;c[e+8>>2]=a;c[e+4>>2]=b;c[e>>2]=d;i=e;return}function Ue(b,d,e,f,g,h){b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;var j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;j=i;i=i+144|0;k=j;l=j+52|0;m=j+48|0;n=j+40|0;o=j+36|0;p=j+32|0;q=j+28|0;r=j+24|0;s=j+20|0;t=j+16|0;u=j+12|0;v=j+64|0;w=j+56|0;x=j+8|0;c[m>>2]=b;c[j+44>>2]=d;c[n>>2]=e;c[o>>2]=f;c[p>>2]=g;c[q>>2]=h;c[r>>2]=c[c[m>>2]>>2];a[w]=32;c[q>>2]=c[q>>2]&-28673;c[o>>2]=(c[o>>2]|0)-((c[(c[n>>2]|0)+4>>2]|0)/2|0);c[p>>2]=(c[p>>2]|0)-((c[(c[n>>2]|0)+4>>2]|0)/2|0);h=Z(c[o>>2]|0,c[(c[r>>2]|0)+40>>2]|0)|0;c[o>>2]=(h|0)/(c[(c[n>>2]|0)+4>>2]|0)|0;h=Z(c[p>>2]|0,c[(c[r>>2]|0)+40>>2]|0)|0;c[p>>2]=(h|0)/(c[(c[n>>2]|0)+4>>2]|0)|0;c[o>>2]=(c[o>>2]|0)+(c[(c[r>>2]|0)+24>>2]|0);c[p>>2]=(c[p>>2]|0)+(c[(c[r>>2]|0)+28>>2]|0);c[s>>2]=Ec(c[r>>2]|0,c[o>>2]|0,c[p>>2]|0)|0;if((c[s>>2]|0)==0){c[l>>2]=0;y=c[l>>2]|0;i=j;return y|0}c[t>>2]=((c[s>>2]|0)-(c[(c[r>>2]|0)+12>>2]|0)|0)/16|0;c[x>>2]=a[(c[(c[m>>2]|0)+8>>2]|0)+(c[t>>2]|0)|0]|0;m=c[q>>2]|0;do{if((m|0)==513){a[w]=117}else if((m|0)==514){q=c[x>>2]|0;if((q|0)==1){a[w]=110;break}else if((q|0)==0|(q|0)==2){a[w]=117;break}else{break}}else if((m|0)==512){q=c[x>>2]|0;if((q|0)==1){a[w]=121;break}else if((q|0)==2|(q|0)==0){a[w]=117;break}else{break}}else{c[l>>2]=0;y=c[l>>2]|0;i=j;return y|0}}while(0);x=a[w]|0;c[k>>2]=c[t>>2];c[k+4>>2]=x;cb(v|0,2336,k|0)|0;c[u>>2]=bg(v)|0;c[l>>2]=c[u>>2];y=c[l>>2]|0;i=j;return y|0}function Ve(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0;e=i;i=i+32|0;f=e+16|0;g=e+12|0;h=e+8|0;j=e+4|0;k=e;c[g>>2]=b;c[h>>2]=d;c[k>>2]=Ke(c[g>>2]|0)|0;if((a[c[h>>2]|0]|0)==83){c[h>>2]=(c[h>>2]|0)+1;c[(c[k>>2]|0)+20>>2]=1}while(1){if((a[c[h>>2]|0]|0)==0){break}c[j>>2]=Kh(c[h>>2]|0)|0;if((c[j>>2]|0)<0){l=13;break}if((c[j>>2]|0)>=(c[(c[c[k>>2]>>2]|0)+8>>2]|0)){l=13;break}g=Eh(c[h>>2]|0,2320)|0;c[h>>2]=(c[h>>2]|0)+g;g=c[h>>2]|0;c[h>>2]=g+1;d=a[g]|0;if((d|0)==110){a[(c[(c[k>>2]|0)+8>>2]|0)+(c[j>>2]|0)|0]=2;continue}else if((d|0)==121){a[(c[(c[k>>2]|0)+8>>2]|0)+(c[j>>2]|0)|0]=0;continue}else if((d|0)==117){a[(c[(c[k>>2]|0)+8>>2]|0)+(c[j>>2]|0)|0]=1;continue}else{l=13;break}}if((l|0)==13){Le(c[k>>2]|0);c[f>>2]=0;m=c[f>>2]|0;i=e;return m|0}if((sf(c[k>>2]|0)|0)!=0){c[(c[k>>2]|0)+16>>2]=1}c[f>>2]=c[k>>2];m=c[f>>2]|0;i=e;return m|0}function We(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0;f=i;i=i+48|0;g=f+32|0;h=f+28|0;j=f+24|0;k=f+20|0;l=f+16|0;m=f+12|0;n=f+8|0;o=f+4|0;p=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;Pc(c[2264+(c[(c[g>>2]|0)+12>>2]<<2)>>2]|0,c[c[g>>2]>>2]|0,c[(c[g>>2]|0)+4>>2]|0,p,l,m);g=Z(c[l>>2]|0,c[h>>2]|0)|0;c[n>>2]=(g|0)/(c[p>>2]|0)|0;g=Z(c[m>>2]|0,c[h>>2]|0)|0;c[o>>2]=(g|0)/(c[p>>2]|0)|0;c[c[j>>2]>>2]=(c[n>>2]|0)+(((c[h>>2]|0)/2|0)<<1)+1;c[c[k>>2]>>2]=(c[o>>2]|0)+(((c[h>>2]|0)/2|0)<<1)+1;i=f;return}function Xe(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0;f=i;i=i+16|0;g=f+8|0;h=f;c[f+12>>2]=a;c[g>>2]=b;c[f+4>>2]=d;c[h>>2]=e;c[(c[g>>2]|0)+4>>2]=c[h>>2];i=f;return}function Ye(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,h=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;h=d;c[e>>2]=a;c[f>>2]=b;c[h>>2]=_f(84)|0;Md(c[e>>2]|0,c[h>>2]|0);g[(c[h>>2]|0)+12>>2]=0.0;g[(c[h>>2]|0)+16>>2]=0.0;g[(c[h>>2]|0)+20>>2]=0.0;g[(c[h>>2]|0)+24>>2]=+g[c[h>>2]>>2]*.8999999761581421;g[(c[h>>2]|0)+28>>2]=+g[(c[h>>2]|0)+4>>2]*.8999999761581421;g[(c[h>>2]|0)+32>>2]=0.0;g[(c[h>>2]|0)+36>>2]=1.0;g[(c[h>>2]|0)+40>>2]=1.0;g[(c[h>>2]|0)+44>>2]=1.0;g[(c[h>>2]|0)+48>>2]=1.0;g[(c[h>>2]|0)+52>>2]=0.0;g[(c[h>>2]|0)+56>>2]=0.0;g[(c[h>>2]|0)+60>>2]=0.0;g[(c[h>>2]|0)+64>>2]=0.0;g[(c[h>>2]|0)+68>>2]=0.0;g[(c[h>>2]|0)+72>>2]=+g[c[h>>2]>>2]*.8999999761581421;g[(c[h>>2]|0)+76>>2]=+g[(c[h>>2]|0)+4>>2]*.8999999761581421;g[(c[h>>2]|0)+80>>2]=+g[(c[h>>2]|0)+8>>2]*.8999999761581421;c[c[f>>2]>>2]=7;i=d;return c[h>>2]|0}function Ze(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0;d=i;i=i+32|0;e=d+16|0;f=d+12|0;g=d+8|0;h=d+4|0;j=d;c[d+20>>2]=a;c[e>>2]=b;c[f>>2]=_f(32)|0;c[g>>2]=c[c[c[e>>2]>>2]>>2];c[h>>2]=c[(c[c[e>>2]>>2]|0)+8>>2];c[(c[f>>2]|0)+4>>2]=0;c[c[f>>2]>>2]=0;e=_f(c[h>>2]|0)|0;c[(c[f>>2]|0)+20>>2]=e;e=_f(c[g>>2]|0)|0;c[(c[f>>2]|0)+24>>2]=e;e=_f(c[g>>2]|0)|0;c[(c[f>>2]|0)+28>>2]=e;e=_f(c[g>>2]<<2)|0;c[(c[f>>2]|0)+12>>2]=e;e=_f(c[g>>2]<<2)|0;c[(c[f>>2]|0)+16>>2]=e;c[(c[f>>2]|0)+8>>2]=0;Oh(c[(c[f>>2]|0)+20>>2]|0,1,c[h>>2]|0)|0;Oh(c[(c[f>>2]|0)+24>>2]|0,0,c[g>>2]|0)|0;Oh(c[(c[f>>2]|0)+28>>2]|0,0,c[g>>2]|0)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[g>>2]|0)){break}c[(c[(c[f>>2]|0)+16>>2]|0)+(c[j>>2]<<2)>>2]=-1;c[(c[(c[f>>2]|0)+12>>2]|0)+(c[j>>2]<<2)>>2]=-1;c[j>>2]=(c[j>>2]|0)+1}i=d;return c[f>>2]|0}function _e(a,b){a=a|0;b=b|0;var d=0,e=0;d=i;i=i+16|0;e=d;c[d+4>>2]=a;c[e>>2]=b;$f(c[(c[e>>2]|0)+12>>2]|0);$f(c[(c[e>>2]|0)+16>>2]|0);$f(c[(c[e>>2]|0)+24>>2]|0);$f(c[(c[e>>2]|0)+28>>2]|0);$f(c[(c[e>>2]|0)+20>>2]|0);$f(c[e>>2]|0);i=d;return}function $e(b,e,f,h,j,k,l,m){b=b|0;e=e|0;f=f|0;h=h|0;j=j|0;k=k|0;l=+l;m=+m;var n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0,L=0,M=0,N=0,O=0,P=0,Q=0,R=0,S=0,T=0,U=0,V=0,W=0,X=0,Y=0,_=0;n=i;i=i+272|0;o=n+264|0;p=n+260|0;q=n+252|0;r=n+236|0;s=n+232|0;t=n+228|0;u=n+224|0;v=n+220|0;w=n+216|0;x=n+152|0;y=n+144|0;z=n+80|0;A=n+76|0;B=n+72|0;C=n+68|0;D=n+64|0;E=n+60|0;F=n+56|0;G=n+268|0;H=n+52|0;I=n+48|0;J=n+44|0;K=n+40|0;L=n+36|0;M=n+32|0;N=n+28|0;O=n+24|0;P=n+20|0;Q=n+16|0;R=n+12|0;S=n+8|0;T=n+4|0;U=n;c[o>>2]=b;c[p>>2]=e;c[n+256>>2]=f;c[q>>2]=h;c[n+248>>2]=j;c[n+244>>2]=k;g[n+240>>2]=l;g[r>>2]=m;c[s>>2]=c[c[q>>2]>>2];c[t>>2]=(c[(c[p>>2]|0)+4>>2]|0)/2|0;c[w>>2]=0;c[y>>2]=0;c[A>>2]=0;if((c[c[p>>2]>>2]|0)==0){c[w>>2]=1}c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[c[s>>2]>>2]|0)){break}c[B>>2]=(c[(c[s>>2]|0)+4>>2]|0)+((c[u>>2]|0)*24|0);c[C>>2]=c[c[B>>2]>>2];c[F>>2]=a[(c[(c[q>>2]|0)+4>>2]|0)+(c[u>>2]|0)|0]|0;do{if((c[F>>2]|0)>=0){k=jf(c[q>>2]|0,c[u>>2]|0,0)|0;if((k|0)>(c[F>>2]|0)){V=1}else{k=jf(c[q>>2]|0,c[u>>2]|0,2)|0;V=(k|0)>((c[C>>2]|0)-(c[F>>2]|0)|0)}c[D>>2]=V&1;k=jf(c[q>>2]|0,c[u>>2]|0,0)|0;if((k|0)==(c[F>>2]|0)){k=jf(c[q>>2]|0,c[u>>2]|0,2)|0;W=(k|0)==((c[C>>2]|0)-(c[F>>2]|0)|0)}else{W=0}c[E>>2]=W&1;if((c[D>>2]|0)==(a[(c[(c[p>>2]|0)+24>>2]|0)+(c[u>>2]|0)|0]|0)?(c[E>>2]|0)==(a[(c[(c[p>>2]|0)+28>>2]|0)+(c[u>>2]|0)|0]|0):0){break}a[(c[(c[p>>2]|0)+24>>2]|0)+(c[u>>2]|0)|0]=c[D>>2];a[(c[(c[p>>2]|0)+28>>2]|0)+(c[u>>2]|0)|0]=c[E>>2];if((c[A>>2]|0)==16){c[w>>2]=1;break}else{k=c[u>>2]|0;j=c[A>>2]|0;c[A>>2]=j+1;c[z+(j<<2)>>2]=k;break}}}while(0);c[u>>2]=(c[u>>2]|0)+1}if(+g[r>>2]>0.0?+g[r>>2]<=.1666666716337204|+g[r>>2]>=.3333333432674408:0){c[v>>2]=((c[(c[p>>2]|0)+8>>2]|0)!=0^1)&1;c[(c[p>>2]|0)+8>>2]=1}else{c[v>>2]=c[(c[p>>2]|0)+8>>2];c[(c[p>>2]|0)+8>>2]=0}c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[(c[s>>2]|0)+8>>2]|0)){break}if((d[(c[(c[q>>2]|0)+12>>2]|0)+(c[u>>2]|0)|0]|0)!=0){X=3}else{X=a[(c[(c[q>>2]|0)+8>>2]|0)+(c[u>>2]|0)|0]|0}a[G]=X;if((a[G]|0)==(a[(c[(c[p>>2]|0)+20>>2]|0)+(c[u>>2]|0)|0]|0)){if((c[v>>2]|0)!=0?(a[(c[(c[q>>2]|0)+8>>2]|0)+(c[u>>2]|0)|0]|0)==0:0){Y=27}}else{Y=27}do{if((Y|0)==27){Y=0;a[(c[(c[p>>2]|0)+20>>2]|0)+(c[u>>2]|0)|0]=a[G]|0;if((c[y>>2]|0)==16){c[w>>2]=1;break}else{r=c[u>>2]|0;E=c[y>>2]|0;c[y>>2]=E+1;c[x+(E<<2)>>2]=r;break}}}while(0);c[u>>2]=(c[u>>2]|0)+1}if((c[w>>2]|0)!=0){c[H>>2]=(c[(c[s>>2]|0)+32>>2]|0)-(c[(c[s>>2]|0)+24>>2]|0);c[I>>2]=(c[(c[s>>2]|0)+36>>2]|0)-(c[(c[s>>2]|0)+28>>2]|0);w=Z(c[H>>2]|0,c[(c[p>>2]|0)+4>>2]|0)|0;c[J>>2]=(w|0)/(c[(c[s>>2]|0)+40>>2]|0)|0;w=Z(c[I>>2]|0,c[(c[p>>2]|0)+4>>2]|0)|0;c[K>>2]=(w|0)/(c[(c[s>>2]|0)+40>>2]|0)|0;kf(c[o>>2]|0,c[p>>2]|0,c[q>>2]|0,0,0,(c[J>>2]|0)+(c[t>>2]<<1)+1|0,(c[K>>2]|0)+(c[t>>2]<<1)+1|0);_=c[p>>2]|0;c[_>>2]=1;i=n;return}c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[A>>2]|0)){break}c[L>>2]=(c[(c[s>>2]|0)+4>>2]|0)+((c[z+(c[u>>2]<<2)>>2]|0)*24|0);lf(c[p>>2]|0,c[s>>2]|0,c[L>>2]|0,M,N,O,P);kf(c[o>>2]|0,c[p>>2]|0,c[q>>2]|0,c[M>>2]|0,c[N>>2]|0,c[O>>2]|0,c[P>>2]|0);c[u>>2]=(c[u>>2]|0)+1}c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[y>>2]|0)){break}c[Q>>2]=(c[(c[s>>2]|0)+12>>2]|0)+(c[x+(c[u>>2]<<2)>>2]<<4);mf(c[p>>2]|0,c[s>>2]|0,c[Q>>2]|0,R,S,T,U);kf(c[o>>2]|0,c[p>>2]|0,c[q>>2]|0,c[R>>2]|0,c[S>>2]|0,c[T>>2]|0,c[U>>2]|0);c[u>>2]=(c[u>>2]|0)+1}_=c[p>>2]|0;c[_>>2]=1;i=n;return}function af(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0;f=i;i=i+16|0;c[f+12>>2]=a;c[f+8>>2]=b;c[f+4>>2]=d;c[f>>2]=e;i=f;return 0.0}function bf(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,h=0,j=0,k=0,l=0.0;f=i;i=i+32|0;h=f+16|0;j=f+12|0;k=f+8|0;c[j>>2]=a;c[k>>2]=b;c[f+4>>2]=d;c[f>>2]=e;if((((c[(c[j>>2]|0)+16>>2]|0)==0?(c[(c[k>>2]|0)+16>>2]|0)!=0:0)?(c[(c[j>>2]|0)+20>>2]|0)==0:0)?(c[(c[k>>2]|0)+20>>2]|0)==0:0){g[h>>2]=.5;l=+g[h>>2];i=f;return+l}g[h>>2]=0.0;l=+g[h>>2];i=f;return+l}function cf(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;i=b;return((c[(c[d>>2]|0)+16>>2]|0)!=0?1:0)|0}function df(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,h=0,j=0,k=0,l=0;e=i;i=i+32|0;f=e+16|0;h=e+12|0;j=e+8|0;k=e+4|0;l=e;c[f>>2]=a;c[h>>2]=b;c[j>>2]=d;We(c[f>>2]|0,700,k,l);g[c[h>>2]>>2]=+(c[k>>2]|0)/100.0;g[c[j>>2]>>2]=+(c[l>>2]|0)/100.0;i=e;return}function ef(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0;f=i;i=i+208|0;g=f+24|0;j=f+184|0;k=f+180|0;l=f+176|0;m=f+172|0;n=f+168|0;o=f+132|0;p=f+128|0;q=f+124|0;r=f+120|0;s=f+116|0;t=f+112|0;u=f+188|0;v=f+108|0;w=f+104|0;x=f+100|0;y=f+96|0;z=f+92|0;A=f+88|0;B=f+84|0;C=f+80|0;D=f+16|0;E=f+8|0;F=f;G=f+48|0;H=f+40|0;I=f+36|0;J=f+32|0;K=f+28|0;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=uc(c[j>>2]|0,0)|0;c[o>>2]=f+136;c[p>>2]=c[c[k>>2]>>2];c[(c[o>>2]|0)+4>>2]=c[l>>2];l=_f(c[c[p>>2]>>2]<<2)|0;c[(c[o>>2]|0)+12>>2]=l;l=_f(c[c[p>>2]>>2]<<2)|0;c[(c[o>>2]|0)+16>>2]=l;c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[c[p>>2]>>2]|0)){break}c[(c[(c[o>>2]|0)+16>>2]|0)+(c[n>>2]<<2)>>2]=-1;c[(c[(c[o>>2]|0)+12>>2]|0)+(c[n>>2]<<2)>>2]=-1;c[n>>2]=(c[n>>2]|0)+1}c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[(c[p>>2]|0)+16>>2]|0)){break}gf(c[o>>2]|0,c[p>>2]|0,c[(c[(c[p>>2]|0)+20>>2]|0)+((c[n>>2]|0)*20|0)+12>>2]|0,c[(c[(c[p>>2]|0)+20>>2]|0)+((c[n>>2]|0)*20|0)+16>>2]|0,q,r);nc(c[j>>2]|0,c[q>>2]|0,c[r>>2]|0,(c[(c[o>>2]|0)+4>>2]|0)/15|0,c[m>>2]|0,c[m>>2]|0);c[n>>2]=(c[n>>2]|0)+1}c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[c[p>>2]>>2]|0)){break}c[s>>2]=(c[(c[p>>2]|0)+4>>2]|0)+((c[n>>2]|0)*24|0);c[t>>2]=a[(c[(c[k>>2]|0)+4>>2]|0)+(c[n>>2]|0)|0]|0;if((c[t>>2]|0)>=0){c[g>>2]=a[(c[(c[k>>2]|0)+4>>2]|0)+(c[n>>2]|0)|0]|0;cb(u|0,2200,g|0)|0;hf(c[o>>2]|0,c[p>>2]|0,c[s>>2]|0,v,w);ic(c[j>>2]|0,c[v>>2]|0,c[w>>2]|0,1,(c[(c[o>>2]|0)+4>>2]|0)/2|0,257,c[m>>2]|0,u)}c[n>>2]=(c[n>>2]|0)+1}c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[(c[p>>2]|0)+8>>2]|0)){break}c[x>>2]=(a[(c[(c[k>>2]|0)+8>>2]|0)+(c[n>>2]|0)|0]|0)==0?30:150;c[y>>2]=(c[(c[p>>2]|0)+12>>2]|0)+(c[n>>2]<<4);gf(c[o>>2]|0,c[p>>2]|0,c[(c[c[y>>2]>>2]|0)+12>>2]|0,c[(c[c[y>>2]>>2]|0)+16>>2]|0,z,A);gf(c[o>>2]|0,c[p>>2]|0,c[(c[(c[y>>2]|0)+4>>2]|0)+12>>2]|0,c[(c[(c[y>>2]|0)+4>>2]|0)+16>>2]|0,B,C);a:do{if((a[(c[(c[k>>2]|0)+8>>2]|0)+(c[n>>2]|0)|0]|0)==0){h[D>>3]=+N(+((+(c[z>>2]|0)- +(c[B>>2]|0))*(+(c[z>>2]|0)- +(c[B>>2]|0))+(+(c[A>>2]|0)- +(c[C>>2]|0))*(+(c[A>>2]|0)- +(c[C>>2]|0))));h[E>>3]=+((c[B>>2]|0)-(c[z>>2]|0)|0)/+h[D>>3];h[F>>3]=+((c[C>>2]|0)-(c[A>>2]|0)|0)/+h[D>>3];h[E>>3]=+h[E>>3]*+(c[(c[o>>2]|0)+4>>2]|0)/+(c[x>>2]|0);h[F>>3]=+h[F>>3]*+(c[(c[o>>2]|0)+4>>2]|0)/+(c[x>>2]|0);c[G>>2]=(c[z>>2]|0)+~~+h[F>>3];c[G+4>>2]=(c[A>>2]|0)-~~+h[E>>3];c[G+8>>2]=(c[z>>2]|0)-~~+h[F>>3];c[G+12>>2]=(c[A>>2]|0)+~~+h[E>>3];c[G+16>>2]=(c[B>>2]|0)-~~+h[F>>3];c[G+20>>2]=(c[C>>2]|0)+~~+h[E>>3];c[G+24>>2]=(c[B>>2]|0)+~~+h[F>>3];c[G+28>>2]=(c[C>>2]|0)-~~+h[E>>3];mc(c[j>>2]|0,G,4,c[m>>2]|0,c[m>>2]|0)}else{c[H>>2]=6;c[I>>2]=1;while(1){if((c[I>>2]|0)>=(c[H>>2]|0)){break a}u=Z(c[z>>2]|0,(c[H>>2]|0)-(c[I>>2]|0)|0)|0;w=u+(Z(c[B>>2]|0,c[I>>2]|0)|0)|0;c[J>>2]=(w|0)/(c[H>>2]|0)|0;w=Z(c[A>>2]|0,(c[H>>2]|0)-(c[I>>2]|0)|0)|0;u=w+(Z(c[C>>2]|0,c[I>>2]|0)|0)|0;c[K>>2]=(u|0)/(c[H>>2]|0)|0;nc(c[j>>2]|0,c[J>>2]|0,c[K>>2]|0,(c[(c[o>>2]|0)+4>>2]|0)/(c[x>>2]|0)|0,c[m>>2]|0,c[m>>2]|0);c[I>>2]=(c[I>>2]|0)+1}}}while(0);c[n>>2]=(c[n>>2]|0)+1}$f(c[(c[o>>2]|0)+12>>2]|0);$f(c[(c[o>>2]|0)+16>>2]|0);i=f;return}function ff(a,b){a=a|0;b=b|0;var d=0;d=i;i=i+16|0;c[d+4>>2]=a;c[d>>2]=b;i=d;return 1}function gf(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0;h=i;i=i+32|0;j=h+20|0;k=h+16|0;l=h+12|0;m=h+8|0;n=h+4|0;o=h;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=f;c[o>>2]=g;c[c[n>>2]>>2]=(c[l>>2]|0)-(c[(c[k>>2]|0)+24>>2]|0);c[c[o>>2]>>2]=(c[m>>2]|0)-(c[(c[k>>2]|0)+28>>2]|0);m=Z(c[c[n>>2]>>2]|0,c[(c[j>>2]|0)+4>>2]|0)|0;c[c[n>>2]>>2]=(m|0)/(c[(c[k>>2]|0)+40>>2]|0)|0;m=Z(c[c[o>>2]>>2]|0,c[(c[j>>2]|0)+4>>2]|0)|0;c[c[o>>2]>>2]=(m|0)/(c[(c[k>>2]|0)+40>>2]|0)|0;k=c[n>>2]|0;c[k>>2]=(c[k>>2]|0)+((c[(c[j>>2]|0)+4>>2]|0)/2|0);k=c[o>>2]|0;c[k>>2]=(c[k>>2]|0)+((c[(c[j>>2]|0)+4>>2]|0)/2|0);i=h;return}function hf(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0;g=i;i=i+32|0;h=g+20|0;j=g+16|0;k=g+12|0;l=g+8|0;m=g+4|0;n=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=((c[k>>2]|0)-(c[(c[j>>2]|0)+4>>2]|0)|0)/24|0;if((c[(c[(c[h>>2]|0)+12>>2]|0)+(c[n>>2]<<2)>>2]|0)>=0){c[c[l>>2]>>2]=c[(c[(c[h>>2]|0)+12>>2]|0)+(c[n>>2]<<2)>>2];c[c[m>>2]>>2]=c[(c[(c[h>>2]|0)+16>>2]|0)+(c[n>>2]<<2)>>2];i=g;return}else{Gc(c[k>>2]|0);gf(c[h>>2]|0,c[j>>2]|0,c[(c[k>>2]|0)+16>>2]|0,c[(c[k>>2]|0)+20>>2]|0,(c[(c[h>>2]|0)+12>>2]|0)+(c[n>>2]<<2)|0,(c[(c[h>>2]|0)+16>>2]|0)+(c[n>>2]<<2)|0);c[c[l>>2]>>2]=c[(c[(c[h>>2]|0)+12>>2]|0)+(c[n>>2]<<2)>>2];c[c[m>>2]>>2]=c[(c[(c[h>>2]|0)+16>>2]|0)+(c[n>>2]<<2)>>2];i=g;return}}function jf(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;f=i;i=i+32|0;g=f+24|0;h=f+20|0;j=f+28|0;k=f+16|0;l=f+12|0;m=f+8|0;n=f+4|0;o=f;c[g>>2]=b;c[h>>2]=d;a[j]=e;c[k>>2]=0;c[l>>2]=c[c[g>>2]>>2];c[m>>2]=(c[(c[l>>2]|0)+4>>2]|0)+((c[h>>2]|0)*24|0);c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[c[m>>2]>>2]|0)){break}c[o>>2]=c[(c[(c[m>>2]|0)+4>>2]|0)+(c[n>>2]<<2)>>2];if((a[(c[(c[g>>2]|0)+8>>2]|0)+(((c[o>>2]|0)-(c[(c[l>>2]|0)+12>>2]|0)|0)/16|0)|0]|0)==(a[j]|0)){c[k>>2]=(c[k>>2]|0)+1}c[n>>2]=(c[n>>2]|0)+1}i=f;return c[k>>2]|0}function kf(b,d,e,f,g,h,j){b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;k=i;i=i+64|0;l=k+52|0;m=k+48|0;n=k+44|0;o=k+40|0;p=k+36|0;q=k+32|0;r=k+28|0;s=k+24|0;t=k+20|0;u=k+16|0;v=k+12|0;w=k+8|0;x=k+4|0;y=k;c[l>>2]=b;c[m>>2]=d;c[n>>2]=e;c[o>>2]=f;c[p>>2]=g;c[q>>2]=h;c[r>>2]=j;c[s>>2]=c[c[n>>2]>>2];pc(c[l>>2]|0,c[o>>2]|0,c[p>>2]|0,c[q>>2]|0,c[r>>2]|0);jc(c[l>>2]|0,c[o>>2]|0,c[p>>2]|0,c[q>>2]|0,c[r>>2]|0,0);c[t>>2]=0;while(1){if((c[t>>2]|0)>=(c[c[s>>2]>>2]|0)){break}if((a[(c[(c[n>>2]|0)+4>>2]|0)+(c[t>>2]|0)|0]|0)>=0?(lf(c[m>>2]|0,c[s>>2]|0,(c[(c[s>>2]|0)+4>>2]|0)+((c[t>>2]|0)*24|0)|0,v,w,x,y),(nf(c[o>>2]|0,c[p>>2]|0,c[q>>2]|0,c[r>>2]|0,c[v>>2]|0,c[w>>2]|0,c[x>>2]|0,c[y>>2]|0)|0)!=0):0){of(c[l>>2]|0,c[m>>2]|0,c[n>>2]|0,c[t>>2]|0)}c[t>>2]=(c[t>>2]|0)+1}c[u>>2]=0;while(1){j=(c[u>>2]|0)>>>0<5;c[t>>2]=0;if(!j){break}while(1){if((c[t>>2]|0)>=(c[(c[s>>2]|0)+8>>2]|0)){break}mf(c[m>>2]|0,c[s>>2]|0,(c[(c[s>>2]|0)+12>>2]|0)+(c[t>>2]<<4)|0,v,w,x,y);if((nf(c[o>>2]|0,c[p>>2]|0,c[q>>2]|0,c[r>>2]|0,c[v>>2]|0,c[w>>2]|0,c[x>>2]|0,c[y>>2]|0)|0)!=0){pf(c[l>>2]|0,c[m>>2]|0,c[n>>2]|0,c[t>>2]|0,c[u>>2]|0)}c[t>>2]=(c[t>>2]|0)+1}c[u>>2]=(c[u>>2]|0)+1}while(1){if((c[t>>2]|0)>=(c[(c[s>>2]|0)+16>>2]|0)){break}qf(c[m>>2]|0,c[s>>2]|0,(c[(c[s>>2]|0)+20>>2]|0)+((c[t>>2]|0)*20|0)|0,v,w,x,y);if((nf(c[o>>2]|0,c[p>>2]|0,c[q>>2]|0,c[r>>2]|0,c[v>>2]|0,c[w>>2]|0,c[x>>2]|0,c[y>>2]|0)|0)!=0){rf(c[l>>2]|0,c[m>>2]|0,c[n>>2]|0,c[t>>2]|0)}c[t>>2]=(c[t>>2]|0)+1}qc(c[l>>2]|0);oc(c[l>>2]|0,c[o>>2]|0,c[p>>2]|0,c[q>>2]|0,c[r>>2]|0);i=k;return}function lf(a,b,d,e,f,g,h){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;var j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;j=i;i=i+48|0;k=j+32|0;l=j+28|0;m=j+24|0;n=j+20|0;o=j+16|0;p=j+12|0;q=j+8|0;r=j+4|0;s=j;c[k>>2]=a;c[l>>2]=b;c[m>>2]=d;c[n>>2]=e;c[o>>2]=f;c[p>>2]=g;c[q>>2]=h;hf(c[k>>2]|0,c[l>>2]|0,c[m>>2]|0,r,s);c[c[n>>2]>>2]=(c[r>>2]|0)-((c[(c[k>>2]|0)+4>>2]|0)/4|0)-1;c[c[o>>2]>>2]=(c[s>>2]|0)-((c[(c[k>>2]|0)+4>>2]|0)/4|0)-3;c[c[p>>2]>>2]=((c[(c[k>>2]|0)+4>>2]|0)/2|0)+2;c[c[q>>2]>>2]=((c[(c[k>>2]|0)+4>>2]|0)/2|0)+5;i=j;return}function mf(a,b,d,e,f,g,h){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;var j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;j=i;i=i+64|0;k=j+56|0;l=j+52|0;m=j+48|0;n=j+44|0;o=j+40|0;p=j+36|0;q=j+32|0;r=j+28|0;s=j+24|0;t=j+20|0;u=j+16|0;v=j+12|0;w=j+8|0;x=j+4|0;y=j;c[k>>2]=a;c[l>>2]=b;c[m>>2]=d;c[n>>2]=e;c[o>>2]=f;c[p>>2]=g;c[q>>2]=h;c[r>>2]=c[(c[c[m>>2]>>2]|0)+12>>2];c[s>>2]=c[(c[c[m>>2]>>2]|0)+16>>2];c[t>>2]=c[(c[(c[m>>2]|0)+4>>2]|0)+12>>2];c[u>>2]=c[(c[(c[m>>2]|0)+4>>2]|0)+16>>2];gf(c[k>>2]|0,c[l>>2]|0,c[r>>2]|0,c[s>>2]|0,r,s);gf(c[k>>2]|0,c[l>>2]|0,c[t>>2]|0,c[u>>2]|0,t,u);c[v>>2]=((c[r>>2]|0)<(c[t>>2]|0)?c[r>>2]|0:c[t>>2]|0)-2;c[w>>2]=((c[r>>2]|0)>(c[t>>2]|0)?c[r>>2]|0:c[t>>2]|0)+2;c[x>>2]=((c[s>>2]|0)<(c[u>>2]|0)?c[s>>2]|0:c[u>>2]|0)-2;c[y>>2]=((c[s>>2]|0)>(c[u>>2]|0)?c[s>>2]|0:c[u>>2]|0)+2;c[c[n>>2]>>2]=c[v>>2];c[c[o>>2]>>2]=c[x>>2];c[c[p>>2]>>2]=(c[w>>2]|0)-(c[v>>2]|0)+1;c[c[q>>2]>>2]=(c[y>>2]|0)-(c[x>>2]|0)+1;i=j;return}function nf(a,b,d,e,f,g,h,j){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0;k=i;i=i+32|0;l=k+28|0;m=k+24|0;n=k+20|0;o=k+16|0;p=k+12|0;q=k+8|0;r=k+4|0;s=k;c[l>>2]=a;c[m>>2]=b;c[n>>2]=d;c[o>>2]=e;c[p>>2]=f;c[q>>2]=g;c[r>>2]=h;c[s>>2]=j;if((c[l>>2]|0)>=((c[p>>2]|0)+(c[r>>2]|0)|0)){t=0;u=t&1;i=k;return u|0}if((c[p>>2]|0)>=((c[l>>2]|0)+(c[n>>2]|0)|0)){t=0;u=t&1;i=k;return u|0}if((c[m>>2]|0)>=((c[q>>2]|0)+(c[s>>2]|0)|0)){t=0;u=t&1;i=k;return u|0}t=(c[q>>2]|0)<((c[m>>2]|0)+(c[o>>2]|0)|0);u=t&1;i=k;return u|0}function of(b,d,e,f){b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;g=i;i=i+64|0;h=g;j=g+32|0;k=g+28|0;l=g+24|0;m=g+20|0;n=g+16|0;o=g+12|0;p=g+8|0;q=g+4|0;r=g+36|0;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=c[c[l>>2]>>2];c[o>>2]=(c[(c[n>>2]|0)+4>>2]|0)+((c[m>>2]|0)*24|0);c[h>>2]=a[(c[(c[l>>2]|0)+4>>2]|0)+(c[m>>2]|0)|0]|0;cb(r|0,2200,h|0)|0;hf(c[k>>2]|0,c[n>>2]|0,c[o>>2]|0,p,q);o=c[j>>2]|0;j=c[p>>2]|0;p=c[q>>2]|0;q=(c[(c[k>>2]|0)+4>>2]|0)/2|0;if((a[(c[(c[k>>2]|0)+24>>2]|0)+(c[m>>2]|0)|0]|0)!=0){s=4;ic(o,j,p,1,q,257,s,r);i=g;return}s=(a[(c[(c[k>>2]|0)+28>>2]|0)+(c[m>>2]|0)|0]|0)!=0?5:1;ic(o,j,p,1,q,257,s,r);i=g;return}function pf(b,d,e,f,g){b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0;h=i;i=i+64|0;j=h+48|0;k=h+44|0;l=h+40|0;m=h+36|0;n=h+32|0;o=h+28|0;p=h+24|0;q=h+20|0;r=h+16|0;s=h+12|0;t=h+8|0;u=h+4|0;v=h;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=g;c[o>>2]=c[c[l>>2]>>2];c[p>>2]=(c[(c[o>>2]|0)+12>>2]|0)+(c[m>>2]<<4);do{if((a[(c[(c[l>>2]|0)+12>>2]|0)+(c[m>>2]|0)|0]|0)==0){if((a[(c[(c[l>>2]|0)+8>>2]|0)+(c[m>>2]|0)|0]|0)==1){c[u>>2]=2;break}if((a[(c[(c[l>>2]|0)+8>>2]|0)+(c[m>>2]|0)|0]|0)==2){c[u>>2]=6;break}if((c[(c[k>>2]|0)+8>>2]|0)!=0){c[u>>2]=3;break}else{c[u>>2]=1;break}}else{c[u>>2]=4}}while(0);if((c[u>>2]|0)!=(c[2208+(c[n>>2]<<2)>>2]|0)){i=h;return}gf(c[k>>2]|0,c[o>>2]|0,c[(c[c[p>>2]>>2]|0)+12>>2]|0,c[(c[c[p>>2]>>2]|0)+16>>2]|0,q,s);gf(c[k>>2]|0,c[o>>2]|0,c[(c[(c[p>>2]|0)+4>>2]|0)+12>>2]|0,c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0,r,t);if((c[u>>2]|0)!=6){lc(c[j>>2]|0,3.0,+(c[q>>2]|0)+.5,+(c[s>>2]|0)+.5,+(c[r>>2]|0)+.5,+(c[t>>2]|0)+.5,c[u>>2]|0);i=h;return}if((c[558]|0)<0){c[v>>2]=bb(2240)|0;if((c[v>>2]|0)!=0?(a[c[v>>2]|0]|0)!=121:0){w=(a[c[v>>2]|0]|0)==89}else{w=1}c[558]=w&1}if((c[558]|0)==0){i=h;return}kc(c[j>>2]|0,c[q>>2]|0,c[s>>2]|0,c[r>>2]|0,c[t>>2]|0,c[u>>2]|0);i=h;return}function qf(a,b,d,e,f,g,h){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;var j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;j=i;i=i+48|0;k=j+32|0;l=j+28|0;m=j+24|0;n=j+20|0;o=j+16|0;p=j+12|0;q=j+8|0;r=j+4|0;s=j;c[k>>2]=a;c[l>>2]=b;c[m>>2]=d;c[n>>2]=e;c[o>>2]=f;c[p>>2]=g;c[q>>2]=h;gf(c[k>>2]|0,c[l>>2]|0,c[(c[m>>2]|0)+12>>2]|0,c[(c[m>>2]|0)+16>>2]|0,r,s);c[c[n>>2]>>2]=(c[r>>2]|0)-2;c[c[o>>2]>>2]=(c[s>>2]|0)-2;c[c[p>>2]>>2]=5;c[c[q>>2]>>2]=5;i=j;return}function rf(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;f=i;i=i+32|0;g=f+28|0;h=f+24|0;j=f+20|0;k=f+16|0;l=f+12|0;m=f+8|0;n=f+4|0;o=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=c[c[j>>2]>>2];c[m>>2]=(c[(c[l>>2]|0)+20>>2]|0)+((c[k>>2]|0)*20|0);gf(c[h>>2]|0,c[l>>2]|0,c[(c[m>>2]|0)+12>>2]|0,c[(c[m>>2]|0)+16>>2]|0,n,o);nc(c[g>>2]|0,c[n>>2]|0,c[o>>2]|0,2,1,1);i=f;return}function sf(b){b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0;d=i;i=i+112|0;e=d+96|0;f=d+92|0;g=d+88|0;h=d+84|0;j=d+80|0;k=d+76|0;l=d+72|0;m=d+68|0;n=d+64|0;o=d+60|0;p=d+56|0;q=d+52|0;r=d+48|0;s=d+44|0;t=d+40|0;u=d+36|0;v=d+32|0;w=d+28|0;x=d+24|0;y=d+20|0;z=d+16|0;A=d+12|0;B=d+8|0;C=d+4|0;D=d;c[f>>2]=b;c[g>>2]=c[c[f>>2]>>2];c[j>>2]=c[c[g>>2]>>2];c[n>>2]=0;c[o>>2]=0;Oh(c[(c[f>>2]|0)+12>>2]|0,0,c[(c[g>>2]|0)+8>>2]|0)|0;c[h>>2]=_f((c[j>>2]|0)+1<<2)|0;wc(c[h>>2]|0,(c[j>>2]|0)+1|0);c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[(c[g>>2]|0)+8>>2]|0)){break}c[p>>2]=(c[(c[g>>2]|0)+12>>2]|0)+(c[k>>2]<<4);if((c[(c[p>>2]|0)+8>>2]|0)!=0){E=((c[(c[p>>2]|0)+8>>2]|0)-(c[(c[g>>2]|0)+4>>2]|0)|0)/24|0}else{E=c[j>>2]|0}c[q>>2]=E;if((c[(c[p>>2]|0)+12>>2]|0)!=0){F=((c[(c[p>>2]|0)+12>>2]|0)-(c[(c[g>>2]|0)+4>>2]|0)|0)/24|0}else{F=c[j>>2]|0}c[r>>2]=F;if((a[(c[(c[f>>2]|0)+8>>2]|0)+(c[k>>2]|0)|0]|0)!=0){Ac(c[h>>2]|0,c[q>>2]|0,c[r>>2]|0)}c[k>>2]=(c[k>>2]|0)+1}c[l>>2]=yc(c[h>>2]|0,c[j>>2]|0)|0;c[m>>2]=-1;c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[(c[g>>2]|0)+8>>2]|0)){break}c[s>>2]=(c[(c[g>>2]|0)+12>>2]|0)+(c[k>>2]<<4);if((c[(c[s>>2]|0)+8>>2]|0)!=0){G=((c[(c[s>>2]|0)+8>>2]|0)-(c[(c[g>>2]|0)+4>>2]|0)|0)/24|0}else{G=c[j>>2]|0}c[t>>2]=G;c[u>>2]=yc(c[h>>2]|0,c[t>>2]|0)|0;if((c[(c[s>>2]|0)+12>>2]|0)!=0){H=((c[(c[s>>2]|0)+12>>2]|0)-(c[(c[g>>2]|0)+4>>2]|0)|0)/24|0}else{H=c[j>>2]|0}c[v>>2]=H;c[w>>2]=yc(c[h>>2]|0,c[v>>2]|0)|0;do{if((a[(c[(c[f>>2]|0)+8>>2]|0)+(c[k>>2]|0)|0]|0)==0){if((c[u>>2]|0)==(c[w>>2]|0)){c[o>>2]=1;break}a[(c[(c[f>>2]|0)+12>>2]|0)+(c[k>>2]|0)|0]=1;if((c[n>>2]|0)==0){c[n>>2]=1}if((c[n>>2]|0)!=2){do{if((c[m>>2]|0)==-1){if((c[u>>2]|0)!=(c[l>>2]|0)){c[m>>2]=c[u>>2];break}else{c[m>>2]=c[w>>2];break}}}while(0);if((c[m>>2]|0)!=-1){if((c[u>>2]|0)!=(c[l>>2]|0)?(c[u>>2]|0)!=(c[m>>2]|0):0){c[n>>2]=2;break}if((c[w>>2]|0)!=(c[l>>2]|0)?(c[w>>2]|0)!=(c[m>>2]|0):0){c[n>>2]=2}}}}}while(0);c[k>>2]=(c[k>>2]|0)+1}$f(c[h>>2]|0);if((c[n>>2]|0)==1?(c[o>>2]|0)==0:0){c[x>>2]=0;c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[j>>2]|0)){break}c[y>>2]=a[(c[(c[f>>2]|0)+4>>2]|0)+(c[k>>2]|0)|0]|0;if((c[y>>2]|0)>=0?(o=jf(c[f>>2]|0,c[k>>2]|0,0)|0,(o|0)!=(c[y>>2]|0)):0){I=44;break}c[k>>2]=(c[k>>2]|0)+1}if((I|0)==44){c[x>>2]=1}if((c[x>>2]|0)==0){Oh(c[(c[f>>2]|0)+12>>2]|0,0,c[(c[g>>2]|0)+8>>2]|0)|0;c[e>>2]=1;J=c[e>>2]|0;i=d;return J|0}}c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[(c[g>>2]|0)+16>>2]|0)){break}c[z>>2]=tf(c[f>>2]|0,c[k>>2]|0,0)|0;c[A>>2]=tf(c[f>>2]|0,c[k>>2]|0,1)|0;if((c[z>>2]|0)==1?(c[A>>2]|0)==0:0){I=53}else{I=52}if((I|0)==52?(I=0,(c[z>>2]|0)>=3):0){I=53}a:do{if((I|0)==53){I=0;c[B>>2]=(c[(c[g>>2]|0)+20>>2]|0)+((c[k>>2]|0)*20|0);c[C>>2]=0;while(1){if((c[C>>2]|0)>=(c[c[B>>2]>>2]|0)){break a}c[D>>2]=((c[(c[(c[B>>2]|0)+4>>2]|0)+(c[C>>2]<<2)>>2]|0)-(c[(c[g>>2]|0)+12>>2]|0)|0)/16|0;if((a[(c[(c[f>>2]|0)+8>>2]|0)+(c[D>>2]|0)|0]|0)==0){a[(c[(c[f>>2]|0)+12>>2]|0)+(c[D>>2]|0)|0]=1}c[C>>2]=(c[C>>2]|0)+1}}}while(0);c[k>>2]=(c[k>>2]|0)+1}c[e>>2]=0;J=c[e>>2]|0;i=d;return J|0}function tf(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;f=i;i=i+32|0;g=f+24|0;h=f+20|0;j=f+28|0;k=f+16|0;l=f+12|0;m=f+8|0;n=f+4|0;o=f;c[g>>2]=b;c[h>>2]=d;a[j]=e;c[k>>2]=0;c[l>>2]=c[c[g>>2]>>2];c[m>>2]=(c[(c[l>>2]|0)+20>>2]|0)+((c[h>>2]|0)*20|0);c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[c[m>>2]>>2]|0)){break}c[o>>2]=c[(c[(c[m>>2]|0)+4>>2]|0)+(c[n>>2]<<2)>>2];if((a[(c[(c[g>>2]|0)+8>>2]|0)+(((c[o>>2]|0)-(c[(c[l>>2]|0)+12>>2]|0)|0)/16|0)|0]|0)==(a[j]|0)){c[k>>2]=(c[k>>2]|0)+1}c[n>>2]=(c[n>>2]|0)+1}i=f;return c[k>>2]|0}function uf(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0;d=i;i=i+32|0;e=d+24|0;f=d+20|0;g=d+16|0;h=d+12|0;j=d+8|0;k=d+4|0;l=d;c[e>>2]=a;c[f>>2]=b;c[h>>2]=c[(c[c[e>>2]>>2]|0)+16>>2];c[j>>2]=c[c[c[e>>2]>>2]>>2];c[k>>2]=c[(c[c[e>>2]>>2]|0)+8>>2];c[l>>2]=_f(52)|0;b=Ke(c[e>>2]|0)|0;c[c[l>>2]>>2]=b;c[(c[l>>2]|0)+4>>2]=3;c[(c[l>>2]|0)+12>>2]=c[f>>2];b=xc(c[h>>2]|0)|0;c[(c[l>>2]|0)+40>>2]=b;b=_f(c[h>>2]<<2)|0;c[(c[l>>2]|0)+8>>2]=b;c[g>>2]=0;while(1){if((c[g>>2]|0)>=(c[h>>2]|0)){break}c[(c[(c[l>>2]|0)+8>>2]|0)+(c[g>>2]<<2)>>2]=1;c[g>>2]=(c[g>>2]|0)+1}g=_f(c[h>>2]|0)|0;c[(c[l>>2]|0)+32>>2]=g;g=_f(c[j>>2]|0)|0;c[(c[l>>2]|0)+36>>2]=g;Oh(c[(c[l>>2]|0)+32>>2]|0,0,c[h>>2]|0)|0;Oh(c[(c[l>>2]|0)+36>>2]|0,0,c[j>>2]|0)|0;g=_f(c[h>>2]|0)|0;c[(c[l>>2]|0)+16>>2]=g;Oh(c[(c[l>>2]|0)+16>>2]|0,0,c[h>>2]|0)|0;g=_f(c[h>>2]|0)|0;c[(c[l>>2]|0)+20>>2]=g;Oh(c[(c[l>>2]|0)+20>>2]|0,0,c[h>>2]|0)|0;h=_f(c[j>>2]|0)|0;c[(c[l>>2]|0)+24>>2]=h;Oh(c[(c[l>>2]|0)+24>>2]|0,0,c[j>>2]|0)|0;h=_f(c[j>>2]|0)|0;c[(c[l>>2]|0)+28>>2]=h;Oh(c[(c[l>>2]|0)+28>>2]|0,0,c[j>>2]|0)|0;if((c[f>>2]|0)<1){c[(c[l>>2]|0)+44>>2]=0}else{j=_f(c[k>>2]<<1)|0;c[(c[l>>2]|0)+44>>2]=j;Oh(c[(c[l>>2]|0)+44>>2]|0,0,c[k>>2]<<1|0)|0}if((c[f>>2]|0)<3){c[(c[l>>2]|0)+48>>2]=0;m=c[l>>2]|0;i=d;return m|0}else{f=xc(c[(c[c[e>>2]>>2]|0)+8>>2]|0)|0;c[(c[l>>2]|0)+48>>2]=f;m=c[l>>2]|0;i=d;return m|0}return 0}function vf(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;b=i;i=i+32|0;d=b+24|0;e=b+20|0;f=b+16|0;g=b+12|0;h=b+8|0;j=b+4|0;k=b;c[e>>2]=a;c[g>>2]=0;c[h>>2]=0;c[j>>2]=0;c[f>>2]=zf(c[e>>2]|0)|0;while(1){if((c[g>>2]|0)>=4){break}l=c[f>>2]|0;if((c[(c[f>>2]|0)+4>>2]|0)==1){m=4;break}if((c[l+4>>2]|0)==0){break}if((c[(c[f>>2]|0)+4>>2]|0)==2){break}if(!((c[2520+(c[g>>2]<<2)>>2]|0)<(c[h>>2]|0)?(c[g>>2]|0)<(c[j>>2]|0):0)){m=9}if(((m|0)==9?(m=0,(c[2520+(c[g>>2]<<2)>>2]|0)<=(c[(c[f>>2]|0)+12>>2]|0)):0)?(c[k>>2]=Lb[c[2536+(c[g>>2]<<2)>>2]&15](c[f>>2]|0)|0,(c[k>>2]|0)!=4):0){c[h>>2]=c[k>>2];c[j>>2]=c[g>>2];c[g>>2]=0;continue}c[g>>2]=(c[g>>2]|0)+1}if((m|0)==4){c[d>>2]=l;n=c[d>>2]|0;i=b;return n|0}if((c[(c[f>>2]|0)+4>>2]|0)!=0?(c[(c[f>>2]|0)+4>>2]|0)!=2:0){c[d>>2]=c[f>>2];n=c[d>>2]|0;i=b;return n|0}Af(c[(c[c[f>>2]>>2]|0)+8>>2]|0,1,2,c[(c[c[c[f>>2]>>2]>>2]|0)+8>>2]|0);c[d>>2]=c[f>>2];n=c[d>>2]|0;i=b;return n|0}function wf(b){b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;d=i;i=i+32|0;e=d;f=d+24|0;g=d+20|0;h=d+16|0;j=d+12|0;k=d+8|0;l=d+4|0;c[f>>2]=b;c[l>>2]=c[(c[c[f>>2]>>2]|0)+8>>2];c[g>>2]=1;b=yf(c[l>>2]|0)|0;c[g>>2]=(c[g>>2]|0)+b;c[g>>2]=(c[g>>2]|0)+(c[l>>2]|0);c[h>>2]=_f((c[g>>2]|0)+1|0)|0;c[j>>2]=c[h>>2];b=cb(c[j>>2]|0,2440,e|0)|0;c[j>>2]=(c[j>>2]|0)+b;c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[l>>2]|0)){break}b=a[(c[(c[f>>2]|0)+8>>2]|0)+(c[k>>2]|0)|0]|0;if((b|0)==2){m=c[j>>2]|0;c[e>>2]=c[k>>2];n=cb(m|0,2456,e|0)|0;c[j>>2]=(c[j>>2]|0)+n}else if((b|0)==0){b=c[j>>2]|0;c[e>>2]=c[k>>2];n=cb(b|0,2448,e|0)|0;c[j>>2]=(c[j>>2]|0)+n}c[k>>2]=(c[k>>2]|0)+1}k=Nh(c[h>>2]|0)|0;if(k>>>0<=(c[g>>2]|0)>>>0){i=d;return c[h>>2]|0}else{Ca(2464,2368,802,2496)}return 0}function xf(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[d>>2]|0)==0){i=b;return}Le(c[c[d>>2]>>2]|0);$f(c[(c[d>>2]|0)+40>>2]|0);$f(c[(c[d>>2]|0)+8>>2]|0);$f(c[(c[d>>2]|0)+32>>2]|0);$f(c[(c[d>>2]|0)+36>>2]|0);$f(c[(c[d>>2]|0)+16>>2]|0);$f(c[(c[d>>2]|0)+20>>2]|0);$f(c[(c[d>>2]|0)+24>>2]|0);$f(c[(c[d>>2]|0)+28>>2]|0);$f(c[(c[d>>2]|0)+44>>2]|0);$f(c[(c[d>>2]|0)+48>>2]|0);$f(c[d>>2]|0);i=b;return}function yf(a){a=a|0;var b=0,d=0,e=0,f=0,g=0;b=i;i=i+16|0;d=b+8|0;e=b+4|0;f=b;c[d>>2]=a;c[e>>2]=1;c[f>>2]=1;while(1){if((c[f>>2]|0)>=(c[d>>2]|0)){break}if(((c[d>>2]|0)-(c[f>>2]|0)|0)>0){g=(c[d>>2]|0)-(c[f>>2]|0)|0}else{g=0}c[e>>2]=(c[e>>2]|0)+g;c[f>>2]=(c[f>>2]|0)*10}i=b;return c[e>>2]|0}function zf(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0;b=i;i=i+32|0;d=b+20|0;e=b+16|0;f=b+12|0;g=b+8|0;h=b+4|0;j=b;c[d>>2]=a;c[e>>2]=c[c[d>>2]>>2];c[f>>2]=c[(c[c[e>>2]>>2]|0)+16>>2];c[g>>2]=c[c[c[e>>2]>>2]>>2];c[h>>2]=c[(c[c[e>>2]>>2]|0)+8>>2];c[j>>2]=_f(52)|0;a=Ke(c[c[d>>2]>>2]|0)|0;c[e>>2]=a;c[c[j>>2]>>2]=a;c[(c[j>>2]|0)+4>>2]=c[(c[d>>2]|0)+4>>2];c[(c[j>>2]|0)+12>>2]=c[(c[d>>2]|0)+12>>2];a=_f(c[f>>2]<<2)|0;c[(c[j>>2]|0)+40>>2]=a;a=_f(c[f>>2]<<2)|0;c[(c[j>>2]|0)+8>>2]=a;Qh(c[(c[j>>2]|0)+40>>2]|0,c[(c[d>>2]|0)+40>>2]|0,c[f>>2]<<2|0)|0;Qh(c[(c[j>>2]|0)+8>>2]|0,c[(c[d>>2]|0)+8>>2]|0,c[f>>2]<<2|0)|0;a=_f(c[f>>2]|0)|0;c[(c[j>>2]|0)+32>>2]=a;a=_f(c[g>>2]|0)|0;c[(c[j>>2]|0)+36>>2]=a;Qh(c[(c[j>>2]|0)+32>>2]|0,c[(c[d>>2]|0)+32>>2]|0,c[f>>2]|0)|0;Qh(c[(c[j>>2]|0)+36>>2]|0,c[(c[d>>2]|0)+36>>2]|0,c[g>>2]|0)|0;a=_f(c[f>>2]|0)|0;c[(c[j>>2]|0)+16>>2]=a;Qh(c[(c[j>>2]|0)+16>>2]|0,c[(c[d>>2]|0)+16>>2]|0,c[f>>2]|0)|0;a=_f(c[f>>2]|0)|0;c[(c[j>>2]|0)+20>>2]=a;Qh(c[(c[j>>2]|0)+20>>2]|0,c[(c[d>>2]|0)+20>>2]|0,c[f>>2]|0)|0;f=_f(c[g>>2]|0)|0;c[(c[j>>2]|0)+24>>2]=f;Qh(c[(c[j>>2]|0)+24>>2]|0,c[(c[d>>2]|0)+24>>2]|0,c[g>>2]|0)|0;f=_f(c[g>>2]|0)|0;c[(c[j>>2]|0)+28>>2]=f;Qh(c[(c[j>>2]|0)+28>>2]|0,c[(c[d>>2]|0)+28>>2]|0,c[g>>2]|0)|0;if((c[(c[d>>2]|0)+44>>2]|0)!=0){g=_f(c[h>>2]<<1)|0;c[(c[j>>2]|0)+44>>2]=g;Qh(c[(c[j>>2]|0)+44>>2]|0,c[(c[d>>2]|0)+44>>2]|0,c[h>>2]<<1|0)|0}else{c[(c[j>>2]|0)+44>>2]=0}if((c[(c[d>>2]|0)+48>>2]|0)!=0){g=_f(c[h>>2]<<2)|0;c[(c[j>>2]|0)+48>>2]=g;Qh(c[(c[j>>2]|0)+48>>2]|0,c[(c[d>>2]|0)+48>>2]|0,c[h>>2]<<2|0)|0;k=c[j>>2]|0;i=b;return k|0}else{c[(c[j>>2]|0)+48>>2]=0;k=c[j>>2]|0;i=b;return k|0}return 0}function Af(b,d,e,f){b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;g=i;i=i+32|0;h=g+16|0;j=g+21|0;k=g+20|0;l=g+12|0;m=g+8|0;n=g+4|0;o=g;c[h>>2]=b;a[j]=d;a[k]=e;c[l>>2]=f;c[m>>2]=c[h>>2];c[n>>2]=c[m>>2];c[o>>2]=c[l>>2];while(1){l=Bh(c[m>>2]|0,a[j]|0,c[o>>2]|0)|0;c[m>>2]=l;if((l|0)==0){break}a[c[m>>2]|0]=a[k]|0;c[o>>2]=(c[o>>2]|0)-((c[m>>2]|0)-(c[n>>2]|0));c[n>>2]=c[m>>2]}i=g;return}function Bf(b){b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0;d=i;i=i+96|0;e=d+80|0;f=d+76|0;g=d+72|0;h=d+68|0;j=d+64|0;k=d+60|0;l=d+56|0;m=d+52|0;n=d+48|0;o=d+44|0;p=d+40|0;q=d+36|0;r=d+32|0;s=d+28|0;t=d+24|0;u=d+20|0;v=d+16|0;w=d+12|0;x=d+8|0;y=d+4|0;z=d;c[f>>2]=b;c[k>>2]=c[c[f>>2]>>2];c[l>>2]=c[c[k>>2]>>2];c[m>>2]=4;c[g>>2]=0;a:while(1){if((c[g>>2]|0)>=(c[c[l>>2]>>2]|0)){A=49;break}c[n>>2]=(c[(c[l>>2]|0)+4>>2]|0)+((c[g>>2]|0)*24|0);b:do{if((a[(c[(c[f>>2]|0)+36>>2]|0)+(c[g>>2]|0)|0]|0)==0){c[h>>2]=a[(c[(c[f>>2]|0)+24>>2]|0)+(c[g>>2]|0)|0]|0;c[j>>2]=a[(c[(c[f>>2]|0)+28>>2]|0)+(c[g>>2]|0)|0]|0;b=c[g>>2]|0;if(((c[h>>2]|0)+(c[j>>2]|0)|0)==(c[c[n>>2]>>2]|0)){a[(c[(c[f>>2]|0)+36>>2]|0)+b|0]=1;break}if((a[(c[(c[k>>2]|0)+4>>2]|0)+b|0]|0)>=0){if((a[(c[(c[k>>2]|0)+4>>2]|0)+(c[g>>2]|0)|0]|0)<(c[h>>2]|0)){A=8;break a}if((a[(c[(c[k>>2]|0)+4>>2]|0)+(c[g>>2]|0)|0]|0)==(c[h>>2]|0)){if((Sf(c[f>>2]|0,c[g>>2]|0,1,2)|0)!=0){c[m>>2]=(c[m>>2]|0)<0?c[m>>2]|0:0}a[(c[(c[f>>2]|0)+36>>2]|0)+(c[g>>2]|0)|0]=1;break}if(((c[c[n>>2]>>2]|0)-(a[(c[(c[k>>2]|0)+4>>2]|0)+(c[g>>2]|0)|0]|0)|0)<(c[j>>2]|0)){A=14;break a}if(((c[c[n>>2]>>2]|0)-(a[(c[(c[k>>2]|0)+4>>2]|0)+(c[g>>2]|0)|0]|0)|0)==(c[j>>2]|0)){if((Sf(c[f>>2]|0,c[g>>2]|0,1,0)|0)!=0){c[m>>2]=(c[m>>2]|0)<0?c[m>>2]|0:0}a[(c[(c[f>>2]|0)+36>>2]|0)+(c[g>>2]|0)|0]=1;break}if(((c[c[n>>2]>>2]|0)-(a[(c[(c[k>>2]|0)+4>>2]|0)+(c[g>>2]|0)|0]|0)|0)==((c[j>>2]|0)+1|0)?((c[c[n>>2]>>2]|0)-(c[h>>2]|0)-(c[j>>2]|0)|0)>2:0){c[o>>2]=0;c:while(1){if((c[o>>2]|0)>=(c[c[n>>2]>>2]|0)){break b}c[q>>2]=((c[(c[(c[n>>2]|0)+4>>2]|0)+(c[o>>2]<<2)>>2]|0)-(c[(c[l>>2]|0)+12>>2]|0)|0)/16|0;if(((c[o>>2]|0)+1|0)<(c[c[n>>2]>>2]|0)){B=(c[o>>2]|0)+1|0}else{B=0}c[r>>2]=((c[(c[(c[n>>2]|0)+4>>2]|0)+(B<<2)>>2]|0)-(c[(c[l>>2]|0)+12>>2]|0)|0)/16|0;if((c[(c[(c[l>>2]|0)+12>>2]|0)+(c[q>>2]<<4)>>2]|0)!=(c[(c[(c[l>>2]|0)+12>>2]|0)+(c[r>>2]<<4)>>2]|0)?(c[(c[(c[l>>2]|0)+12>>2]|0)+(c[q>>2]<<4)>>2]|0)!=(c[(c[(c[l>>2]|0)+12>>2]|0)+(c[r>>2]<<4)+4>>2]|0):0){if((c[(c[(c[l>>2]|0)+12>>2]|0)+(c[q>>2]<<4)+4>>2]|0)!=(c[(c[(c[l>>2]|0)+12>>2]|0)+(c[r>>2]<<4)>>2]|0)?(c[(c[(c[l>>2]|0)+12>>2]|0)+(c[q>>2]<<4)+4>>2]|0)!=(c[(c[(c[l>>2]|0)+12>>2]|0)+(c[r>>2]<<4)+4>>2]|0):0){A=30;break a}c[t>>2]=((c[(c[(c[l>>2]|0)+12>>2]|0)+(c[q>>2]<<4)+4>>2]|0)-(c[(c[l>>2]|0)+20>>2]|0)|0)/20|0}else{c[t>>2]=((c[(c[(c[l>>2]|0)+12>>2]|0)+(c[q>>2]<<4)>>2]|0)-(c[(c[l>>2]|0)+20>>2]|0)|0)/20|0}d:do{if((a[(c[(c[k>>2]|0)+8>>2]|0)+(c[q>>2]|0)|0]|0)==1?(a[(c[(c[k>>2]|0)+8>>2]|0)+(c[r>>2]|0)|0]|0)==1:0){c[p>>2]=0;while(1){if((c[p>>2]|0)>=(c[(c[(c[l>>2]|0)+20>>2]|0)+((c[t>>2]|0)*20|0)>>2]|0)){break d}c[u>>2]=((c[(c[(c[(c[l>>2]|0)+20>>2]|0)+((c[t>>2]|0)*20|0)+4>>2]|0)+(c[p>>2]<<2)>>2]|0)-(c[(c[l>>2]|0)+12>>2]|0)|0)/16|0;if((a[(c[(c[k>>2]|0)+8>>2]|0)+(c[u>>2]|0)|0]|0)==0){break c}c[p>>2]=(c[p>>2]|0)+1}}}while(0);c[o>>2]=(c[o>>2]|0)+1}c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[c[n>>2]>>2]|0)){break b}c[s>>2]=((c[(c[(c[n>>2]|0)+4>>2]|0)+(c[o>>2]<<2)>>2]|0)-(c[(c[l>>2]|0)+12>>2]|0)|0)/16|0;if(((a[(c[(c[k>>2]|0)+8>>2]|0)+(c[s>>2]|0)|0]|0)==1?(c[s>>2]|0)!=(c[q>>2]|0):0)?(c[s>>2]|0)!=(c[r>>2]|0):0){c[v>>2]=Gf(c[f>>2]|0,c[s>>2]|0,0)|0;if((c[v>>2]|0)==0){A=45;break a}c[m>>2]=(c[m>>2]|0)<0?c[m>>2]|0:0}c[o>>2]=(c[o>>2]|0)+1}}}}}while(0);c[g>>2]=(c[g>>2]|0)+1}if((A|0)==8){c[(c[f>>2]|0)+4>>2]=1;c[e>>2]=0;C=c[e>>2]|0;i=d;return C|0}else if((A|0)==14){c[(c[f>>2]|0)+4>>2]=1;c[e>>2]=0;C=c[e>>2]|0;i=d;return C|0}else if((A|0)==30){Ca(2832,2368,2037,2920)}else if((A|0)==45){Ca(2944,2368,2061,2920)}else if((A|0)==49){c[g>>2]=0;e:while(1){if((c[g>>2]|0)>=(c[(c[l>>2]|0)+16>>2]|0)){A=68;break}c[w>>2]=(c[(c[l>>2]|0)+20>>2]|0)+((c[g>>2]|0)*20|0);do{if((a[(c[(c[f>>2]|0)+32>>2]|0)+(c[g>>2]|0)|0]|0)==0){c[x>>2]=a[(c[(c[f>>2]|0)+16>>2]|0)+(c[g>>2]|0)|0]|0;c[y>>2]=a[(c[(c[f>>2]|0)+20>>2]|0)+(c[g>>2]|0)|0]|0;c[z>>2]=(c[c[w>>2]>>2]|0)-(c[x>>2]|0)-(c[y>>2]|0);if((c[x>>2]|0)==0){if((c[z>>2]|0)==0){a[(c[(c[f>>2]|0)+32>>2]|0)+(c[g>>2]|0)|0]=1;break}if((c[z>>2]|0)!=1){break}Tf(c[f>>2]|0,c[g>>2]|0,1,2)|0;c[m>>2]=(c[m>>2]|0)<0?c[m>>2]|0:0;a[(c[(c[f>>2]|0)+32>>2]|0)+(c[g>>2]|0)|0]=1;break}if((c[x>>2]|0)==1){if((c[z>>2]|0)==0){A=59;break e}if((c[z>>2]|0)!=1){break}Tf(c[f>>2]|0,c[g>>2]|0,1,0)|0;c[m>>2]=(c[m>>2]|0)<0?c[m>>2]|0:0;break}if((c[x>>2]|0)!=2){A=66;break e}if((c[z>>2]|0)>0){Tf(c[f>>2]|0,c[g>>2]|0,1,2)|0;c[m>>2]=(c[m>>2]|0)<0?c[m>>2]|0:0}a[(c[(c[f>>2]|0)+32>>2]|0)+(c[g>>2]|0)|0]=1}}while(0);c[g>>2]=(c[g>>2]|0)+1}if((A|0)==59){c[(c[f>>2]|0)+4>>2]=1;c[e>>2]=0;C=c[e>>2]|0;i=d;return C|0}else if((A|0)==66){c[(c[f>>2]|0)+4>>2]=1;c[e>>2]=0;C=c[e>>2]|0;i=d;return C|0}else if((A|0)==68){c[e>>2]=c[m>>2];C=c[e>>2]|0;i=d;return C|0}}return 0}function Cf(b){b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0,L=0,M=0,N=0,O=0,P=0,Q=0,R=0,S=0,T=0,U=0,V=0,W=0,X=0,Y=0,Z=0;d=i;i=i+1328|0;e=d+1312|0;f=d+1308|0;g=d+1304|0;h=d+1300|0;j=d+1296|0;k=d+1292|0;l=d+1288|0;m=d+712|0;n=d+136|0;o=d+132|0;p=d+128|0;q=d+124|0;r=d+120|0;s=d+116|0;t=d+112|0;u=d+108|0;v=d+104|0;w=d+100|0;x=d+96|0;y=d+92|0;z=d+88|0;A=d+84|0;B=d+80|0;C=d+76|0;D=d+72|0;E=d+68|0;F=d+64|0;G=d+60|0;H=d+56|0;I=d+52|0;J=d+48|0;K=d+44|0;L=d+40|0;M=d+36|0;N=d+32|0;O=d+28|0;P=d+24|0;Q=d+20|0;R=d+16|0;S=d+12|0;T=d+8|0;U=d+4|0;V=d;c[f>>2]=b;c[g>>2]=c[c[f>>2]>>2];c[h>>2]=c[c[g>>2]>>2];c[j>>2]=c[(c[f>>2]|0)+44>>2];c[l>>2]=4;c[k>>2]=0;a:while(1){if((c[k>>2]|0)>=(c[c[h>>2]>>2]|0)){W=61;break}c[o>>2]=(c[(c[h>>2]|0)+4>>2]|0)+((c[k>>2]|0)*24|0);c[p>>2]=c[c[o>>2]>>2];c[s>>2]=a[(c[(c[g>>2]|0)+4>>2]|0)+(c[k>>2]|0)|0]|0;if((c[p>>2]|0)>12){W=4;break}b:do{if((a[(c[(c[f>>2]|0)+36>>2]|0)+(c[k>>2]|0)|0]|0)==0?(c[s>>2]|0)>=0:0){c[q>>2]=0;while(1){if((c[q>>2]|0)>=(c[p>>2]|0)){break}c[t>>2]=((c[(c[(c[o>>2]|0)+4>>2]|0)+(c[q>>2]<<2)>>2]|0)-(c[(c[h>>2]|0)+12>>2]|0)|0)/16|0;c[v>>2]=a[(c[(c[g>>2]|0)+8>>2]|0)+(c[t>>2]|0)|0]|0;b=(c[q>>2]|0)+1|0;c[y>>2]=b;c[y>>2]=(c[y>>2]|0)>=(c[p>>2]|0)?0:b;c[m+((c[q>>2]|0)*48|0)+(c[y>>2]<<2)>>2]=(c[v>>2]|0)==2?0:1;c[n+((c[q>>2]|0)*48|0)+(c[y>>2]<<2)>>2]=(c[v>>2]|0)==0?1:0;c[u>>2]=Qf(c[h>>2]|0,c[o>>2]|0,c[y>>2]|0)|0;c[t>>2]=((c[(c[(c[o>>2]|0)+4>>2]|0)+(c[y>>2]<<2)>>2]|0)-(c[(c[h>>2]|0)+12>>2]|0)|0)/16|0;c[w>>2]=a[(c[(c[g>>2]|0)+8>>2]|0)+(c[t>>2]|0)|0]|0;b=(c[y>>2]|0)+1|0;c[y>>2]=b;c[y>>2]=(c[y>>2]|0)>=(c[p>>2]|0)?0:b;c[x>>2]=2;if((c[v>>2]|0)==2){c[x>>2]=(c[x>>2]|0)+ -1}if((c[w>>2]|0)==2){c[x>>2]=(c[x>>2]|0)+ -1}if((c[x>>2]|0)==2?(Mf(c[j>>2]|0,c[u>>2]|0)|0)!=0:0){c[x>>2]=1}c[m+((c[q>>2]|0)*48|0)+(c[y>>2]<<2)>>2]=c[x>>2];c[x>>2]=0;if((c[v>>2]|0)==0){c[x>>2]=(c[x>>2]|0)+1}if((c[w>>2]|0)==0){c[x>>2]=(c[x>>2]|0)+1}if((c[x>>2]|0)==0?(Nf(c[j>>2]|0,c[u>>2]|0)|0)!=0:0){c[x>>2]=1}c[n+((c[q>>2]|0)*48|0)+(c[y>>2]<<2)>>2]=c[x>>2];c[q>>2]=(c[q>>2]|0)+1}c[r>>2]=3;while(1){b=(c[r>>2]|0)<(c[p>>2]|0);c[q>>2]=0;if(!b){break}while(1){if((c[q>>2]|0)>=(c[p>>2]|0)){break}c[z>>2]=(c[q>>2]|0)+(c[r>>2]|0);c[A>>2]=(c[q>>2]|0)+1;c[B>>2]=(c[q>>2]|0)+2;if((c[z>>2]|0)>=(c[p>>2]|0)){c[z>>2]=(c[z>>2]|0)-(c[p>>2]|0)}if((c[A>>2]|0)>=(c[p>>2]|0)){c[A>>2]=(c[A>>2]|0)-(c[p>>2]|0)}if((c[B>>2]|0)>=(c[p>>2]|0)){c[B>>2]=(c[B>>2]|0)-(c[p>>2]|0)}c[m+((c[q>>2]|0)*48|0)+(c[z>>2]<<2)>>2]=(c[m+((c[q>>2]|0)*48|0)+(c[A>>2]<<2)>>2]|0)+(c[m+((c[A>>2]|0)*48|0)+(c[z>>2]<<2)>>2]|0);c[n+((c[q>>2]|0)*48|0)+(c[z>>2]<<2)>>2]=(c[n+((c[q>>2]|0)*48|0)+(c[A>>2]<<2)>>2]|0)+(c[n+((c[A>>2]|0)*48|0)+(c[z>>2]<<2)>>2]|0);c[C>>2]=(c[m+((c[q>>2]|0)*48|0)+(c[B>>2]<<2)>>2]|0)+(c[m+((c[B>>2]|0)*48|0)+(c[z>>2]<<2)>>2]|0);if((c[m+((c[q>>2]|0)*48|0)+(c[z>>2]<<2)>>2]|0)<(c[C>>2]|0)){X=c[m+((c[q>>2]|0)*48|0)+(c[z>>2]<<2)>>2]|0}else{X=c[C>>2]|0}c[m+((c[q>>2]|0)*48|0)+(c[z>>2]<<2)>>2]=X;c[C>>2]=(c[n+((c[q>>2]|0)*48|0)+(c[B>>2]<<2)>>2]|0)+(c[n+((c[B>>2]|0)*48|0)+(c[z>>2]<<2)>>2]|0);if((c[n+((c[q>>2]|0)*48|0)+(c[z>>2]<<2)>>2]|0)>(c[C>>2]|0)){Y=c[n+((c[q>>2]|0)*48|0)+(c[z>>2]<<2)>>2]|0}else{Y=c[C>>2]|0}c[n+((c[q>>2]|0)*48|0)+(c[z>>2]<<2)>>2]=Y;c[q>>2]=(c[q>>2]|0)+1}c[r>>2]=(c[r>>2]|0)+1}while(1){if((c[q>>2]|0)>=(c[p>>2]|0)){break b}c[E>>2]=c[(c[(c[o>>2]|0)+4>>2]|0)+(c[q>>2]<<2)>>2];c[F>>2]=((c[E>>2]|0)-(c[(c[h>>2]|0)+12>>2]|0)|0)/16|0;if((a[(c[(c[g>>2]|0)+8>>2]|0)+(c[F>>2]|0)|0]|0)==1){b=(c[q>>2]|0)+1|0;c[D>>2]=b;c[D>>2]=(c[D>>2]|0)>=(c[p>>2]|0)?0:b;if((c[n+((c[D>>2]|0)*48|0)+(c[q>>2]<<2)>>2]|0)>(c[s>>2]|0)){W=44;break a}if((c[n+((c[D>>2]|0)*48|0)+(c[q>>2]<<2)>>2]|0)==(c[s>>2]|0)){Gf(c[f>>2]|0,c[F>>2]|0,2)|0;c[l>>2]=(c[l>>2]|0)<0?c[l>>2]|0:0}if((c[m+((c[D>>2]|0)*48|0)+(c[q>>2]<<2)>>2]|0)<((c[s>>2]|0)-1|0)){W=48;break a}if((c[m+((c[D>>2]|0)*48|0)+(c[q>>2]<<2)>>2]|0)==((c[s>>2]|0)-1|0)){Gf(c[f>>2]|0,c[F>>2]|0,0)|0;c[l>>2]=(c[l>>2]|0)<0?c[l>>2]|0:0}if((c[(c[f>>2]|0)+12>>2]|0)>=2?(c[E>>2]=c[(c[(c[o>>2]|0)+4>>2]|0)+(c[D>>2]<<2)>>2],(a[(c[(c[g>>2]|0)+8>>2]|0)+(((c[E>>2]|0)-(c[(c[h>>2]|0)+12>>2]|0)|0)/16|0)|0]|0)==1):0){c[G>>2]=Qf(c[h>>2]|0,c[o>>2]|0,c[D>>2]|0)|0;b=(c[D>>2]|0)+1|0;c[D>>2]=b;c[D>>2]=(c[D>>2]|0)>=(c[p>>2]|0)?0:b;if((c[n+((c[D>>2]|0)*48|0)+(c[q>>2]<<2)>>2]|0)>((c[s>>2]|0)-2|0)?(Kf(c[j>>2]|0,c[G>>2]|0)|0)!=0:0){c[l>>2]=(c[l>>2]|0)<1?c[l>>2]|0:1}if((c[m+((c[D>>2]|0)*48|0)+(c[q>>2]<<2)>>2]|0)<(c[s>>2]|0)?(Lf(c[j>>2]|0,c[G>>2]|0)|0)!=0:0){c[l>>2]=(c[l>>2]|0)<1?c[l>>2]|0:1}}}c[q>>2]=(c[q>>2]|0)+1}}}while(0);c[k>>2]=(c[k>>2]|0)+1}if((W|0)==4){Ca(2784,2368,2173,2808)}else if((W|0)==44){c[(c[f>>2]|0)+4>>2]=1;c[e>>2]=0;Z=c[e>>2]|0;i=d;return Z|0}else if((W|0)==48){c[(c[f>>2]|0)+4>>2]=1;c[e>>2]=0;Z=c[e>>2]|0;i=d;return Z|0}else if((W|0)==61){if((c[l>>2]|0)<1){c[e>>2]=c[l>>2];Z=c[e>>2]|0;i=d;return Z|0}c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[(c[h>>2]|0)+16>>2]|0)){break}c[H>>2]=(c[(c[h>>2]|0)+20>>2]|0)+((c[k>>2]|0)*20|0);c[I>>2]=c[c[H>>2]>>2];c:do{if((a[(c[(c[f>>2]|0)+32>>2]|0)+(c[k>>2]|0)|0]|0)==0){c[J>>2]=a[(c[(c[f>>2]|0)+16>>2]|0)+(c[k>>2]|0)|0]|0;c[K>>2]=a[(c[(c[f>>2]|0)+20>>2]|0)+(c[k>>2]|0)|0]|0;c[L>>2]=(c[I>>2]|0)-(c[J>>2]|0)-(c[K>>2]|0);c[M>>2]=0;while(1){if((c[M>>2]|0)>=(c[I>>2]|0)){break c}q=(c[M>>2]|0)+1|0;c[N>>2]=q;c[N>>2]=(c[N>>2]|0)>=(c[I>>2]|0)?0:q;c[O>>2]=Jf(c[h>>2]|0,c[H>>2]|0,c[M>>2]|0)|0;c[P>>2]=((c[(c[(c[H>>2]|0)+4>>2]|0)+(c[M>>2]<<2)>>2]|0)-(c[(c[h>>2]|0)+12>>2]|0)|0)/16|0;c[Q>>2]=((c[(c[(c[H>>2]|0)+4>>2]|0)+(c[N>>2]<<2)>>2]|0)-(c[(c[h>>2]|0)+12>>2]|0)|0)/16|0;c[R>>2]=a[(c[(c[g>>2]|0)+8>>2]|0)+(c[P>>2]|0)|0]|0;c[S>>2]=a[(c[(c[g>>2]|0)+8>>2]|0)+(c[Q>>2]|0)|0]|0;if(!((c[R>>2]|0)!=2?(c[S>>2]|0)!=2:0)){W=70}if((W|0)==70?(W=0,(Kf(c[j>>2]|0,c[O>>2]|0)|0)!=0):0){c[l>>2]=(c[l>>2]|0)<1?c[l>>2]|0:1}if(!((c[R>>2]|0)!=0?(c[S>>2]|0)!=0:0)){W=74}if((W|0)==74?(W=0,(Lf(c[j>>2]|0,c[O>>2]|0)|0)!=0):0){c[l>>2]=(c[l>>2]|0)<1?c[l>>2]|0:1}if((Mf(c[j>>2]|0,c[O>>2]|0)|0)!=0){if((c[R>>2]|0)==0?(c[S>>2]|0)==1:0){Gf(c[f>>2]|0,c[Q>>2]|0,2)|0;c[l>>2]=(c[l>>2]|0)<0?c[l>>2]|0:0}if((c[S>>2]|0)==0?(c[R>>2]|0)==1:0){Gf(c[f>>2]|0,c[P>>2]|0,2)|0;c[l>>2]=(c[l>>2]|0)<0?c[l>>2]|0:0}}if((Nf(c[j>>2]|0,c[O>>2]|0)|0)!=0){if((c[R>>2]|0)==2?(c[S>>2]|0)==1:0){Gf(c[f>>2]|0,c[Q>>2]|0,0)|0;c[l>>2]=(c[l>>2]|0)<0?c[l>>2]|0:0}if((c[S>>2]|0)==2?(c[R>>2]|0)==1:0){Gf(c[f>>2]|0,c[P>>2]|0,0)|0;c[l>>2]=(c[l>>2]|0)<0?c[l>>2]|0:0}}d:do{if((c[R>>2]|0)==1?(c[S>>2]|0)==1:0){if((c[J>>2]|0)==0?(c[L>>2]|0)==2:0){if((Mf(c[j>>2]|0,c[O>>2]|0)|0)!=0){Gf(c[f>>2]|0,c[P>>2]|0,2)|0;Gf(c[f>>2]|0,c[Q>>2]|0,2)|0;c[l>>2]=(c[l>>2]|0)<0?c[l>>2]|0:0}if((Nf(c[j>>2]|0,c[O>>2]|0)|0)!=0){Gf(c[f>>2]|0,c[P>>2]|0,0)|0;Gf(c[f>>2]|0,c[Q>>2]|0,0)|0;c[l>>2]=(c[l>>2]|0)<0?c[l>>2]|0:0}}if((c[J>>2]|0)==1){if((Kf(c[j>>2]|0,c[O>>2]|0)|0)!=0){c[l>>2]=(c[l>>2]|0)<1?c[l>>2]|0:1}if((c[L>>2]|0)==2?(Lf(c[j>>2]|0,c[O>>2]|0)|0)!=0:0){c[l>>2]=(c[l>>2]|0)<1?c[l>>2]|0:1}}if((c[(c[f>>2]|0)+12>>2]|0)>=2?(Nf(c[j>>2]|0,c[O>>2]|0)|0)!=0:0){c[T>>2]=0;while(1){if((c[T>>2]|0)>=(c[I>>2]|0)){break}do{if(((c[T>>2]|0)!=(c[M>>2]|0)?(c[T>>2]|0)!=((c[M>>2]|0)+1|0):0)?(c[T>>2]|0)!=((c[M>>2]|0)-1|0):0){if((c[M>>2]|0)==0?(c[T>>2]|0)==((c[I>>2]|0)-1|0):0){break}if((c[M>>2]|0)==((c[I>>2]|0)-1|0)?(c[T>>2]|0)==0:0){break}c[U>>2]=Jf(c[h>>2]|0,c[H>>2]|0,c[T>>2]|0)|0;if((Kf(c[j>>2]|0,c[U>>2]|0)|0)!=0){c[l>>2]=(c[l>>2]|0)<1?c[l>>2]|0:1}}}while(0);c[T>>2]=(c[T>>2]|0)+1}if((c[J>>2]|0)==0?(Mf(c[j>>2]|0,c[O>>2]|0)|0)!=0:0){if((c[L>>2]|0)!=3){if((c[L>>2]|0)!=4){break}if((Rf(c[f>>2]|0,c[H>>2]|0,c[M>>2]|0)|0)==0){break}c[l>>2]=(c[l>>2]|0)<1?c[l>>2]|0:1;break}c[T>>2]=0;while(1){if((c[T>>2]|0)>=(c[I>>2]|0)){break d}if(((c[T>>2]|0)!=(c[M>>2]|0)?(c[T>>2]|0)!=(c[N>>2]|0):0)?(c[V>>2]=((c[(c[(c[H>>2]|0)+4>>2]|0)+(c[T>>2]<<2)>>2]|0)-(c[(c[h>>2]|0)+12>>2]|0)|0)/16|0,(a[(c[(c[g>>2]|0)+8>>2]|0)+(c[V>>2]|0)|0]|0)==1):0){Gf(c[f>>2]|0,c[V>>2]|0,0)|0;c[l>>2]=(c[l>>2]|0)<0?c[l>>2]|0:0}c[T>>2]=(c[T>>2]|0)+1}}}}}while(0);c[M>>2]=(c[M>>2]|0)+1}}}while(0);c[k>>2]=(c[k>>2]|0)+1}c[e>>2]=c[l>>2];Z=c[e>>2]|0;i=d;return Z|0}return 0}function Df(b){b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0;d=i;i=i+128|0;e=d+112|0;f=d+108|0;g=d+104|0;h=d+100|0;j=d+96|0;k=d+92|0;l=d+88|0;m=d+84|0;n=d+80|0;o=d+76|0;p=d+72|0;q=d+68|0;r=d+64|0;s=d+60|0;t=d+56|0;u=d+52|0;v=d+48|0;w=d+44|0;x=d+40|0;y=d+36|0;z=d+32|0;A=d+28|0;B=d+24|0;C=d+20|0;D=d+16|0;E=d+12|0;F=d+8|0;G=d+4|0;H=d;c[e>>2]=b;c[f>>2]=c[c[e>>2]>>2];c[g>>2]=c[c[f>>2]>>2];c[h>>2]=c[(c[e>>2]|0)+44>>2];c[k>>2]=4;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[c[g>>2]>>2]|0)){break}if((a[(c[(c[e>>2]|0)+36>>2]|0)+(c[j>>2]|0)|0]|0)==0?(c[q>>2]=a[(c[(c[f>>2]|0)+4>>2]|0)+(c[j>>2]|0)|0]|0,(c[q>>2]|0)>=0):0){c[m>>2]=c[(c[(c[g>>2]|0)+4>>2]|0)+((c[j>>2]|0)*24|0)>>2];c[n>>2]=a[(c[(c[e>>2]|0)+24>>2]|0)+(c[j>>2]|0)|0]|0;if(((c[n>>2]|0)+1|0)==(c[q>>2]|0)?(Hf(c[e>>2]|0,c[j>>2]|0,2)|0)!=0:0){c[k>>2]=(c[k>>2]|0)<0?c[k>>2]|0:0}c[o>>2]=a[(c[(c[e>>2]|0)+28>>2]|0)+(c[j>>2]|0)|0]|0;if(((c[o>>2]|0)+1|0)==((c[m>>2]|0)-(c[q>>2]|0)|0)?(Hf(c[e>>2]|0,c[j>>2]|0,0)|0)!=0:0){c[k>>2]=(c[k>>2]|0)<0?c[k>>2]|0:0}c[n>>2]=a[(c[(c[e>>2]|0)+24>>2]|0)+(c[j>>2]|0)|0]|0;c[p>>2]=(c[m>>2]|0)-(c[o>>2]|0)-(c[n>>2]|0);c[l>>2]=If(c[e>>2]|0,c[(c[(c[g>>2]|0)+4>>2]|0)+((c[j>>2]|0)*24|0)+4>>2]|0,((c[q>>2]|0)-(c[n>>2]|0)|0)%2|0,c[p>>2]|0)|0;c[k>>2]=(c[k>>2]|0)<(c[l>>2]|0)?c[k>>2]|0:c[l>>2]|0}c[j>>2]=(c[j>>2]|0)+1}c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[(c[g>>2]|0)+16>>2]|0)){break}c[r>>2]=(c[(c[g>>2]|0)+20>>2]|0)+((c[j>>2]|0)*20|0);c[s>>2]=c[c[r>>2]>>2];c[t>>2]=0;while(1){if((c[t>>2]|0)>=(c[s>>2]|0)){break}c[x>>2]=Jf(c[g>>2]|0,c[r>>2]|0,c[t>>2]|0)|0;c[y>>2]=((c[(c[(c[r>>2]|0)+4>>2]|0)+(c[t>>2]<<2)>>2]|0)-(c[(c[g>>2]|0)+12>>2]|0)|0)/16|0;do{if((a[(c[(c[f>>2]|0)+8>>2]|0)+(c[y>>2]|0)|0]|0)==1?(p=(c[t>>2]|0)+1|0,c[E>>2]=p,c[E>>2]=(c[E>>2]|0)==(c[s>>2]|0)?0:p,c[z>>2]=((c[(c[(c[r>>2]|0)+4>>2]|0)+(c[E>>2]<<2)>>2]|0)-(c[(c[g>>2]|0)+12>>2]|0)|0)/16|0,(a[(c[(c[f>>2]|0)+8>>2]|0)+(c[z>>2]|0)|0]|0)==1):0){c[A>>2]=zc(c[(c[e>>2]|0)+48>>2]|0,c[y>>2]|0,C)|0;c[B>>2]=zc(c[(c[e>>2]|0)+48>>2]|0,c[z>>2]|0,D)|0;if((c[A>>2]|0)==(c[B>>2]|0)?(c[C>>2]|0)!=(c[D>>2]|0):0){if((Kf(c[h>>2]|0,c[x>>2]|0)|0)!=0){c[k>>2]=(c[k>>2]|0)<1?c[k>>2]|0:1}if((Lf(c[h>>2]|0,c[x>>2]|0)|0)==0){break}c[k>>2]=(c[k>>2]|0)<1?c[k>>2]|0:1;break}if(((Mf(c[h>>2]|0,c[x>>2]|0)|0)!=0?(Nf(c[h>>2]|0,c[x>>2]|0)|0)!=0:0)?(Of(c[e>>2]|0,c[y>>2]|0,c[z>>2]|0,1)|0)!=0:0){c[k>>2]=(c[k>>2]|0)<3?c[k>>2]|0:3}}}while(0);c[t>>2]=(c[t>>2]|0)+1}c[u>>2]=a[(c[(c[e>>2]|0)+16>>2]|0)+(c[j>>2]|0)|0]|0;c[v>>2]=a[(c[(c[e>>2]|0)+20>>2]|0)+(c[j>>2]|0)|0]|0;c[w>>2]=(c[s>>2]|0)-(c[u>>2]|0)-(c[v>>2]|0);c[l>>2]=If(c[e>>2]|0,c[(c[r>>2]|0)+4>>2]|0,(c[u>>2]|0)%2|0,c[w>>2]|0)|0;c[k>>2]=(c[k>>2]|0)<(c[l>>2]|0)?c[k>>2]|0:c[l>>2]|0;c[j>>2]=(c[j>>2]|0)+1}c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[(c[g>>2]|0)+8>>2]|0)){break}c[F>>2]=zc(c[(c[e>>2]|0)+48>>2]|0,c[j>>2]|0,G)|0;do{if((c[F>>2]|0)!=(c[j>>2]|0)){c[H>>2]=a[(c[(c[c[e>>2]>>2]|0)+8>>2]|0)+(c[F>>2]|0)|0]|0;if((c[H>>2]|0)!=1){l=c[H>>2]|0;if((Gf(c[e>>2]|0,c[j>>2]|0,(c[G>>2]|0)!=0?2-l|0:l)|0)==0){break}c[k>>2]=(c[k>>2]|0)<0?c[k>>2]|0:0;break}c[H>>2]=a[(c[(c[c[e>>2]>>2]|0)+8>>2]|0)+(c[j>>2]|0)|0]|0;if((c[H>>2]|0)!=1?(l=c[H>>2]|0,(Gf(c[e>>2]|0,c[F>>2]|0,(c[G>>2]|0)!=0?2-l|0:l)|0)!=0):0){c[k>>2]=(c[k>>2]|0)<0?c[k>>2]|0:0}}}while(0);c[j>>2]=(c[j>>2]|0)+1}i=d;return c[k>>2]|0}function Ef(b){b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0;d=i;i=i+96|0;e=d+92|0;f=d+88|0;g=d+84|0;h=d+80|0;j=d+76|0;k=d+72|0;l=d+68|0;m=d+64|0;n=d+60|0;o=d+56|0;p=d+52|0;q=d+48|0;r=d+44|0;s=d+40|0;t=d+36|0;u=d+32|0;v=d+28|0;w=d+24|0;x=d+20|0;y=d+16|0;z=d+12|0;A=d+8|0;B=d+4|0;C=d;c[e>>2]=b;c[f>>2]=0;c[g>>2]=0;c[h>>2]=0;c[j>>2]=0;c[k>>2]=c[c[e>>2]>>2];c[l>>2]=c[c[k>>2]>>2];c[m>>2]=c[(c[l>>2]|0)+16>>2];c[n>>2]=0;c[p>>2]=0;c[q>>2]=0;while(1){if((c[q>>2]|0)>=(c[(c[l>>2]|0)+8>>2]|0)){break}if((a[(c[(c[k>>2]|0)+8>>2]|0)+(c[q>>2]|0)|0]|0)==0){b=Ff(c[e>>2]|0,c[q>>2]|0)|0;c[n>>2]=c[n>>2]|b;c[f>>2]=(c[f>>2]|0)+1}c[q>>2]=(c[q>>2]|0)+1}c[q>>2]=0;while(1){if((c[q>>2]|0)>=(c[c[l>>2]>>2]|0)){break}c[r>>2]=a[(c[(c[k>>2]|0)+4>>2]|0)+(c[q>>2]|0)|0]|0;if((c[r>>2]|0)>=0){c[s>>2]=a[(c[(c[e>>2]|0)+24>>2]|0)+(c[q>>2]|0)|0]|0;if((c[s>>2]|0)!=(c[r>>2]|0)){if((c[s>>2]|0)==((c[r>>2]|0)-1|0)){c[j>>2]=(c[j>>2]|0)+1}}else{c[h>>2]=(c[h>>2]|0)+1}c[g>>2]=(c[g>>2]|0)+1}c[q>>2]=(c[q>>2]|0)+1}c[q>>2]=0;while(1){D=c[e>>2]|0;if((c[q>>2]|0)>=(c[(c[l>>2]|0)+16>>2]|0)){break}r=yc(c[D+40>>2]|0,c[q>>2]|0)|0;c[o>>2]=c[(c[(c[e>>2]|0)+8>>2]|0)+(r<<2)>>2];if((c[o>>2]|0)>1){c[m>>2]=(c[m>>2]|0)<(c[o>>2]|0)?c[m>>2]|0:c[o>>2]|0}c[q>>2]=(c[q>>2]|0)+1}if((c[D+4>>2]|0)!=3){Ca(2552,2368,2617,2600)}if((c[h>>2]|0)==(c[g>>2]|0)?(c[m>>2]|0)==(c[f>>2]|0):0){c[(c[e>>2]|0)+4>>2]=0;c[p>>2]=1;E=c[p>>2]|0;F=(E|0)!=0;G=F?0:4;i=d;return G|0}c[q>>2]=0;while(1){if((c[q>>2]|0)>=(c[(c[l>>2]|0)+8>>2]|0)){H=46;break}c[t>>2]=(c[(c[l>>2]|0)+12>>2]|0)+(c[q>>2]<<4);c[u>>2]=((c[c[t>>2]>>2]|0)-(c[(c[l>>2]|0)+20>>2]|0)|0)/20|0;c[v>>2]=((c[(c[t>>2]|0)+4>>2]|0)-(c[(c[l>>2]|0)+20>>2]|0)|0)/20|0;if((a[(c[(c[k>>2]|0)+8>>2]|0)+(c[q>>2]|0)|0]|0)==1?(c[w>>2]=yc(c[(c[e>>2]|0)+40>>2]|0,c[u>>2]|0)|0,m=c[w>>2]|0,(m|0)==(yc(c[(c[e>>2]|0)+40>>2]|0,c[v>>2]|0)|0)):0){c[x>>2]=2;if((c[(c[(c[e>>2]|0)+8>>2]|0)+(c[w>>2]<<2)>>2]|0)==((c[f>>2]|0)+1|0)){c[y>>2]=0;if(((c[(c[t>>2]|0)+8>>2]|0)!=0?(c[z>>2]=((c[(c[t>>2]|0)+8>>2]|0)-(c[(c[l>>2]|0)+4>>2]|0)|0)/24|0,c[A>>2]=a[(c[(c[k>>2]|0)+4>>2]|0)+(c[z>>2]|0)|0]|0,(c[A>>2]|0)>=0):0)?(a[(c[(c[e>>2]|0)+24>>2]|0)+(c[z>>2]|0)|0]|0)==((c[A>>2]|0)-1|0):0){c[y>>2]=(c[y>>2]|0)+1}if(((c[(c[t>>2]|0)+12>>2]|0)!=0?(c[B>>2]=((c[(c[t>>2]|0)+12>>2]|0)-(c[(c[l>>2]|0)+4>>2]|0)|0)/24|0,c[C>>2]=a[(c[(c[k>>2]|0)+4>>2]|0)+(c[B>>2]|0)|0]|0,(c[C>>2]|0)>=0):0)?(a[(c[(c[e>>2]|0)+24>>2]|0)+(c[B>>2]|0)|0]|0)==((c[C>>2]|0)-1|0):0){c[y>>2]=(c[y>>2]|0)+1}if((c[j>>2]|0)==(c[y>>2]|0)?((c[j>>2]|0)+(c[h>>2]|0)|0)==(c[g>>2]|0):0){c[x>>2]=0}}c[p>>2]=Gf(c[e>>2]|0,c[q>>2]|0,c[x>>2]|0)|0;if((c[p>>2]|0)!=1){H=42;break}if((c[x>>2]|0)==0){H=44;break}}c[q>>2]=(c[q>>2]|0)+1}if((H|0)==42){Ca(2616,2368,2711,2600)}else if((H|0)==44){c[(c[e>>2]|0)+4>>2]=2;E=c[p>>2]|0;F=(E|0)!=0;G=F?0:4;i=d;return G|0}else if((H|0)==46){E=c[p>>2]|0;F=(E|0)!=0;G=F?0:4;i=d;return G|0}return 0}function Ff(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;d=i;i=i+32|0;e=d+28|0;f=d+24|0;g=d+20|0;h=d+16|0;j=d+12|0;k=d+8|0;l=d+4|0;m=d;c[f>>2]=a;c[g>>2]=b;c[l>>2]=c[c[c[f>>2]>>2]>>2];c[m>>2]=(c[(c[l>>2]|0)+12>>2]|0)+(c[g>>2]<<4);c[h>>2]=((c[c[m>>2]>>2]|0)-(c[(c[l>>2]|0)+20>>2]|0)|0)/20|0;c[j>>2]=((c[(c[m>>2]|0)+4>>2]|0)-(c[(c[l>>2]|0)+20>>2]|0)|0)/20|0;c[h>>2]=yc(c[(c[f>>2]|0)+40>>2]|0,c[h>>2]|0)|0;c[j>>2]=yc(c[(c[f>>2]|0)+40>>2]|0,c[j>>2]|0)|0;if((c[h>>2]|0)==(c[j>>2]|0)){c[e>>2]=1;n=c[e>>2]|0;i=d;return n|0}else{c[k>>2]=(c[(c[(c[f>>2]|0)+8>>2]|0)+(c[h>>2]<<2)>>2]|0)+(c[(c[(c[f>>2]|0)+8>>2]|0)+(c[j>>2]<<2)>>2]|0);Ac(c[(c[f>>2]|0)+40>>2]|0,c[h>>2]|0,c[j>>2]|0);c[h>>2]=yc(c[(c[f>>2]|0)+40>>2]|0,c[h>>2]|0)|0;c[(c[(c[f>>2]|0)+8>>2]|0)+(c[h>>2]<<2)>>2]=c[k>>2];c[e>>2]=0;n=c[e>>2]|0;i=d;return n|0}return 0}function Gf(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;f=i;i=i+32|0;g=f+24|0;h=f+20|0;j=f+16|0;k=f+12|0;l=f+8|0;m=f+4|0;n=f;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=c[c[h>>2]>>2];if((c[k>>2]|0)==1){Ca(2640,2368,1075,2672)}if((a[(c[(c[l>>2]|0)+8>>2]|0)+(c[j>>2]|0)|0]|0)==(c[k>>2]|0)){c[g>>2]=0;o=c[g>>2]|0;i=f;return o|0}a[(c[(c[l>>2]|0)+8>>2]|0)+(c[j>>2]|0)|0]=c[k>>2];c[m>>2]=c[c[l>>2]>>2];c[n>>2]=(c[(c[m>>2]|0)+12>>2]|0)+(c[j>>2]<<4);j=((c[c[n>>2]>>2]|0)-(c[(c[m>>2]|0)+20>>2]|0)|0)/20|0;l=c[h>>2]|0;if((c[k>>2]|0)==0){k=(c[l+16>>2]|0)+j|0;a[k]=(a[k]|0)+1<<24>>24;k=(c[(c[h>>2]|0)+16>>2]|0)+(((c[(c[n>>2]|0)+4>>2]|0)-(c[(c[m>>2]|0)+20>>2]|0)|0)/20|0)|0;a[k]=(a[k]|0)+1<<24>>24;if((c[(c[n>>2]|0)+8>>2]|0)!=0){k=(c[(c[h>>2]|0)+24>>2]|0)+(((c[(c[n>>2]|0)+8>>2]|0)-(c[(c[m>>2]|0)+4>>2]|0)|0)/24|0)|0;a[k]=(a[k]|0)+1<<24>>24}if((c[(c[n>>2]|0)+12>>2]|0)!=0){k=(c[(c[h>>2]|0)+24>>2]|0)+(((c[(c[n>>2]|0)+12>>2]|0)-(c[(c[m>>2]|0)+4>>2]|0)|0)/24|0)|0;a[k]=(a[k]|0)+1<<24>>24}}else{k=(c[l+20>>2]|0)+j|0;a[k]=(a[k]|0)+1<<24>>24;k=(c[(c[h>>2]|0)+20>>2]|0)+(((c[(c[n>>2]|0)+4>>2]|0)-(c[(c[m>>2]|0)+20>>2]|0)|0)/20|0)|0;a[k]=(a[k]|0)+1<<24>>24;if((c[(c[n>>2]|0)+8>>2]|0)!=0){k=(c[(c[h>>2]|0)+28>>2]|0)+(((c[(c[n>>2]|0)+8>>2]|0)-(c[(c[m>>2]|0)+4>>2]|0)|0)/24|0)|0;a[k]=(a[k]|0)+1<<24>>24}if((c[(c[n>>2]|0)+12>>2]|0)!=0){k=(c[(c[h>>2]|0)+28>>2]|0)+(((c[(c[n>>2]|0)+12>>2]|0)-(c[(c[m>>2]|0)+4>>2]|0)|0)/24|0)|0;a[k]=(a[k]|0)+1<<24>>24}}c[g>>2]=1;o=c[g>>2]|0;i=f;return o|0}function Hf(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0;f=i;i=i+64|0;g=f+60|0;h=f+56|0;j=f+52|0;k=f+48|0;l=f+44|0;m=f+40|0;n=f+36|0;o=f+32|0;p=f+28|0;q=f+24|0;r=f+20|0;s=f+16|0;t=f+12|0;u=f+8|0;v=f+4|0;w=f;c[g>>2]=b;c[h>>2]=d;c[j>>2]=e;c[k>>2]=0;c[l>>2]=c[c[g>>2]>>2];c[m>>2]=c[c[l>>2]>>2];c[n>>2]=(c[(c[m>>2]|0)+4>>2]|0)+((c[h>>2]|0)*24|0);c[o>>2]=c[c[n>>2]>>2];c[p>>2]=0;while(1){if((c[p>>2]|0)>=(c[o>>2]|0)){break}c[v>>2]=((c[(c[(c[n>>2]|0)+4>>2]|0)+(c[p>>2]<<2)>>2]|0)-(c[(c[m>>2]|0)+12>>2]|0)|0)/16|0;a:do{if((a[(c[(c[l>>2]|0)+8>>2]|0)+(c[v>>2]|0)|0]|0)==1){c[q>>2]=(c[p>>2]|0)+1;while(1){if((c[q>>2]|0)>=(c[o>>2]|0)){break a}c[w>>2]=((c[(c[(c[n>>2]|0)+4>>2]|0)+(c[q>>2]<<2)>>2]|0)-(c[(c[m>>2]|0)+12>>2]|0)|0)/16|0;if(((a[(c[(c[l>>2]|0)+8>>2]|0)+(c[w>>2]|0)|0]|0)==1?(c[r>>2]=zc(c[(c[g>>2]|0)+48>>2]|0,c[v>>2]|0,t)|0,c[s>>2]=zc(c[(c[g>>2]|0)+48>>2]|0,c[w>>2]|0,u)|0,(c[r>>2]|0)==(c[s>>2]|0)):0)?(c[t>>2]|0)==(c[u>>2]|0):0){Gf(c[g>>2]|0,c[v>>2]|0,c[j>>2]|0)|0;Gf(c[g>>2]|0,c[w>>2]|0,c[j>>2]|0)|0}c[q>>2]=(c[q>>2]|0)+1}}}while(0);c[p>>2]=(c[p>>2]|0)+1}i=f;return c[k>>2]|0}function If(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0;f=i;i=i+128|0;g=f+120|0;h=f+116|0;j=f+112|0;k=f+108|0;l=f+104|0;m=f+100|0;n=f+96|0;o=f+88|0;p=f+72|0;q=f+60|0;r=f+48|0;s=f+32|0;t=f+16|0;u=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=c[c[g>>2]>>2];c[m>>2]=4;c[n>>2]=c[(c[g>>2]|0)+48>>2];if((c[k>>2]|0)==2){Pf(c[l>>2]|0,c[h>>2]|0,2,o);if((Of(c[g>>2]|0,c[o>>2]|0,c[o+4>>2]|0,c[j>>2]|0)|0)==0){v=c[m>>2]|0;i=f;return v|0}c[m>>2]=(c[m>>2]|0)<3?c[m>>2]|0:3;v=c[m>>2]|0;i=f;return v|0}if((c[k>>2]|0)==3){Pf(c[l>>2]|0,c[h>>2]|0,3,p);c[q>>2]=zc(c[n>>2]|0,c[p>>2]|0,r)|0;c[q+4>>2]=zc(c[n>>2]|0,c[p+4>>2]|0,r+4|0)|0;c[q+8>>2]=zc(c[n>>2]|0,c[p+8>>2]|0,r+8|0)|0;if((c[q>>2]|0)==(c[q+4>>2]|0)?(Gf(c[g>>2]|0,c[p+8>>2]|0,(c[j>>2]^c[r>>2]^c[r+4>>2]|0)!=0?0:2)|0)!=0:0){c[m>>2]=(c[m>>2]|0)<0?c[m>>2]|0:0}if((c[q>>2]|0)==(c[q+8>>2]|0)?(Gf(c[g>>2]|0,c[p+4>>2]|0,(c[j>>2]^c[r>>2]^c[r+8>>2]|0)!=0?0:2)|0)!=0:0){c[m>>2]=(c[m>>2]|0)<0?c[m>>2]|0:0}if((c[q+4>>2]|0)!=(c[q+8>>2]|0)){v=c[m>>2]|0;i=f;return v|0}if((Gf(c[g>>2]|0,c[p>>2]|0,(c[j>>2]^c[r+4>>2]^c[r+8>>2]|0)!=0?0:2)|0)==0){v=c[m>>2]|0;i=f;return v|0}c[m>>2]=(c[m>>2]|0)<0?c[m>>2]|0:0;v=c[m>>2]|0;i=f;return v|0}if((c[k>>2]|0)!=4){v=c[m>>2]|0;i=f;return v|0}Pf(c[l>>2]|0,c[h>>2]|0,4,s);c[t>>2]=zc(c[n>>2]|0,c[s>>2]|0,u)|0;c[t+4>>2]=zc(c[n>>2]|0,c[s+4>>2]|0,u+4|0)|0;c[t+8>>2]=zc(c[n>>2]|0,c[s+8>>2]|0,u+8|0)|0;c[t+12>>2]=zc(c[n>>2]|0,c[s+12>>2]|0,u+12|0)|0;if((c[t>>2]|0)==(c[t+4>>2]|0)){if((Of(c[g>>2]|0,c[s+8>>2]|0,c[s+12>>2]|0,c[j>>2]^c[u>>2]^c[u+4>>2])|0)==0){v=c[m>>2]|0;i=f;return v|0}c[m>>2]=(c[m>>2]|0)<3?c[m>>2]|0:3;v=c[m>>2]|0;i=f;return v|0}if((c[t>>2]|0)==(c[t+8>>2]|0)){if((Of(c[g>>2]|0,c[s+4>>2]|0,c[s+12>>2]|0,c[j>>2]^c[u>>2]^c[u+8>>2])|0)==0){v=c[m>>2]|0;i=f;return v|0}c[m>>2]=(c[m>>2]|0)<3?c[m>>2]|0:3;v=c[m>>2]|0;i=f;return v|0}if((c[t>>2]|0)==(c[t+12>>2]|0)){if((Of(c[g>>2]|0,c[s+4>>2]|0,c[s+8>>2]|0,c[j>>2]^c[u>>2]^c[u+12>>2])|0)==0){v=c[m>>2]|0;i=f;return v|0}c[m>>2]=(c[m>>2]|0)<3?c[m>>2]|0:3;v=c[m>>2]|0;i=f;return v|0}if((c[t+4>>2]|0)==(c[t+8>>2]|0)){if((Of(c[g>>2]|0,c[s>>2]|0,c[s+12>>2]|0,c[j>>2]^c[u+4>>2]^c[u+8>>2])|0)==0){v=c[m>>2]|0;i=f;return v|0}c[m>>2]=(c[m>>2]|0)<3?c[m>>2]|0:3;v=c[m>>2]|0;i=f;return v|0}if((c[t+4>>2]|0)==(c[t+12>>2]|0)){if((Of(c[g>>2]|0,c[s>>2]|0,c[s+8>>2]|0,c[j>>2]^c[u+4>>2]^c[u+12>>2])|0)==0){v=c[m>>2]|0;i=f;return v|0}c[m>>2]=(c[m>>2]|0)<3?c[m>>2]|0:3;v=c[m>>2]|0;i=f;return v|0}if((c[t+8>>2]|0)!=(c[t+12>>2]|0)){v=c[m>>2]|0;i=f;return v|0}if((Of(c[g>>2]|0,c[s>>2]|0,c[s+4>>2]|0,c[j>>2]^c[u+8>>2]^c[u+12>>2])|0)==0){v=c[m>>2]|0;i=f;return v|0}c[m>>2]=(c[m>>2]|0)<3?c[m>>2]|0:3;v=c[m>>2]|0;i=f;return v|0}function Jf(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0;e=i;i=i+32|0;f=e+16|0;g=e+12|0;h=e+8|0;j=e+4|0;k=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;c[j>>2]=c[(c[(c[g>>2]|0)+4>>2]|0)+(c[h>>2]<<2)>>2];c[k>>2]=((((c[j>>2]|0)-(c[(c[f>>2]|0)+12>>2]|0)|0)/16|0)<<1)+((c[c[j>>2]>>2]|0)==(c[g>>2]|0)?1:0);i=e;return c[k>>2]|0}function Kf(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0;e=i;i=i+16|0;f=e+4|0;g=e;c[f>>2]=b;c[g>>2]=d;if((a[(c[f>>2]|0)+(c[g>>2]|0)|0]&2|0)!=0){h=0;i=e;return h|0}d=(c[f>>2]|0)+(c[g>>2]|0)|0;a[d]=a[d]|2;h=1;i=e;return h|0}function Lf(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0;e=i;i=i+16|0;f=e+4|0;g=e;c[f>>2]=b;c[g>>2]=d;if((a[(c[f>>2]|0)+(c[g>>2]|0)|0]&1|0)!=0){h=0;i=e;return h|0}d=(c[f>>2]|0)+(c[g>>2]|0)|0;a[d]=a[d]|1;h=1;i=e;return h|0}function Mf(b,d){b=b|0;d=d|0;var e=0,f=0,g=0;e=i;i=i+16|0;f=e+4|0;g=e;c[f>>2]=b;c[g>>2]=d;i=e;return a[(c[f>>2]|0)+(c[g>>2]|0)|0]&2|0}function Nf(b,d){b=b|0;d=d|0;var e=0,f=0,g=0;e=i;i=i+16|0;f=e+4|0;g=e;c[f>>2]=b;c[g>>2]=d;i=e;return a[(c[f>>2]|0)+(c[g>>2]|0)|0]&1|0}function Of(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0;f=i;i=i+32|0;g=f+16|0;h=f+12|0;j=f+8|0;k=f+4|0;l=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;if((c[h>>2]|0)>=(c[(c[c[c[g>>2]>>2]>>2]|0)+8>>2]|0)){Ca(2688,2368,1164,2728)}if((c[j>>2]|0)<(c[(c[c[c[g>>2]>>2]>>2]|0)+8>>2]|0)){c[h>>2]=zc(c[(c[g>>2]|0)+48>>2]|0,c[h>>2]|0,l)|0;c[k>>2]=c[k>>2]^c[l>>2];c[j>>2]=zc(c[(c[g>>2]|0)+48>>2]|0,c[j>>2]|0,l)|0;c[k>>2]=c[k>>2]^c[l>>2];Bc(c[(c[g>>2]|0)+48>>2]|0,c[h>>2]|0,c[j>>2]|0,c[k>>2]|0);i=f;return(c[h>>2]|0)!=(c[j>>2]|0)|0}else{Ca(2744,2368,1165,2728)}return 0}function Pf(b,d,e,f){b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;g=i;i=i+32|0;h=g+24|0;j=g+20|0;k=g+16|0;l=g+12|0;m=g+8|0;n=g+4|0;o=g;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=f;c[m>>2]=0;c[n>>2]=c[c[h>>2]>>2];while(1){if((c[m>>2]|0)>=(c[k>>2]|0)){break}c[o>>2]=((c[c[j>>2]>>2]|0)-(c[(c[n>>2]|0)+12>>2]|0)|0)/16|0;if((a[(c[(c[h>>2]|0)+8>>2]|0)+(c[o>>2]|0)|0]|0)==1){c[(c[l>>2]|0)+(c[m>>2]<<2)>>2]=c[o>>2];c[m>>2]=(c[m>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+4}i=g;return}function Qf(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0;e=i;i=i+32|0;f=e+20|0;g=e+16|0;h=e+12|0;j=e+8|0;k=e+4|0;l=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;c[j>>2]=c[(c[(c[g>>2]|0)+4>>2]|0)+(c[h>>2]<<2)>>2];c[k>>2]=c[(c[(c[g>>2]|0)+8>>2]|0)+(c[h>>2]<<2)>>2];c[l>>2]=((((c[j>>2]|0)-(c[(c[f>>2]|0)+12>>2]|0)|0)/16|0)<<1)+((c[c[j>>2]>>2]|0)==(c[k>>2]|0)?1:0);i=e;return c[l>>2]|0}function Rf(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;f=i;i=i+48|0;g=f+36|0;h=f+32|0;j=f+28|0;k=f+24|0;l=f+20|0;m=f+16|0;n=f+12|0;o=f+8|0;p=f+4|0;q=f;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=c[c[h>>2]>>2];c[m>>2]=c[c[l>>2]>>2];c[n>>2]=c[c[j>>2]>>2];c[o>>2]=0;a:while(1){if((c[o>>2]|0)>=(c[n>>2]|0)){r=14;break}do{if(((c[o>>2]|0)!=(c[k>>2]|0)?(c[o>>2]|0)!=((c[k>>2]|0)+1|0):0)?(c[o>>2]|0)!=((c[k>>2]|0)-1|0):0){if((c[o>>2]|0)==0?(c[k>>2]|0)==((c[n>>2]|0)-1|0):0){break}if((c[o>>2]|0)==((c[n>>2]|0)-1|0)?(c[k>>2]|0)==0:0){break}e=(c[o>>2]|0)+1|0;c[p>>2]=e;c[p>>2]=(c[p>>2]|0)==(c[n>>2]|0)?0:e;if((a[(c[(c[l>>2]|0)+8>>2]|0)+(((c[(c[(c[j>>2]|0)+4>>2]|0)+(c[o>>2]<<2)>>2]|0)-(c[(c[m>>2]|0)+12>>2]|0)|0)/16|0)|0]|0)==1?(a[(c[(c[l>>2]|0)+8>>2]|0)+(((c[(c[(c[j>>2]|0)+4>>2]|0)+(c[p>>2]<<2)>>2]|0)-(c[(c[m>>2]|0)+12>>2]|0)|0)/16|0)|0]|0)==1:0){r=12;break a}}}while(0);c[o>>2]=(c[o>>2]|0)+1}if((r|0)==12){c[q>>2]=Jf(c[m>>2]|0,c[j>>2]|0,c[o>>2]|0)|0;c[g>>2]=Lf(c[(c[h>>2]|0)+44>>2]|0,c[q>>2]|0)|0;s=c[g>>2]|0;i=f;return s|0}else if((r|0)==14){c[g>>2]=0;s=c[g>>2]|0;i=f;return s|0}return 0}function Sf(b,d,e,f){b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0;g=i;i=i+48|0;h=g+36|0;j=g+32|0;k=g+28|0;l=g+41|0;m=g+40|0;n=g+24|0;o=g+20|0;p=g+16|0;q=g+12|0;r=g+8|0;s=g+4|0;t=g;c[j>>2]=b;c[k>>2]=d;a[l]=e;a[m]=f;c[n>>2]=0;c[p>>2]=c[c[j>>2]>>2];if((a[l]|0)==(a[m]|0)){c[h>>2]=0;u=c[h>>2]|0;i=g;return u|0}c[q>>2]=c[c[p>>2]>>2];c[r>>2]=(c[(c[q>>2]|0)+4>>2]|0)+((c[k>>2]|0)*24|0);c[s>>2]=0;while(1){if((c[s>>2]|0)>=(c[c[r>>2]>>2]|0)){break}c[t>>2]=((c[(c[(c[r>>2]|0)+4>>2]|0)+(c[s>>2]<<2)>>2]|0)-(c[(c[q>>2]|0)+12>>2]|0)|0)/16|0;if((a[(c[(c[p>>2]|0)+8>>2]|0)+(c[t>>2]|0)|0]|0)==(a[l]|0)){c[o>>2]=Gf(c[j>>2]|0,c[t>>2]|0,a[m]|0)|0;if((c[o>>2]|0)!=1){v=7;break}c[n>>2]=1}c[s>>2]=(c[s>>2]|0)+1}if((v|0)==7){Ca(2952,2368,1271,2984)}c[h>>2]=c[n>>2];u=c[h>>2]|0;i=g;return u|0}function Tf(b,d,e,f){b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0;g=i;i=i+48|0;h=g+36|0;j=g+32|0;k=g+28|0;l=g+41|0;m=g+40|0;n=g+24|0;o=g+20|0;p=g+16|0;q=g+12|0;r=g+8|0;s=g+4|0;t=g;c[j>>2]=b;c[k>>2]=d;a[l]=e;a[m]=f;c[n>>2]=0;c[p>>2]=c[c[j>>2]>>2];if((a[l]|0)==(a[m]|0)){c[h>>2]=0;u=c[h>>2]|0;i=g;return u|0}c[q>>2]=c[c[p>>2]>>2];c[r>>2]=(c[(c[q>>2]|0)+20>>2]|0)+((c[k>>2]|0)*20|0);c[s>>2]=0;while(1){if((c[s>>2]|0)>=(c[c[r>>2]>>2]|0)){break}c[t>>2]=((c[(c[(c[r>>2]|0)+4>>2]|0)+(c[s>>2]<<2)>>2]|0)-(c[(c[q>>2]|0)+12>>2]|0)|0)/16|0;if((a[(c[(c[p>>2]|0)+8>>2]|0)+(c[t>>2]|0)|0]|0)==(a[l]|0)){c[o>>2]=Gf(c[j>>2]|0,c[t>>2]|0,a[m]|0)|0;if((c[o>>2]|0)!=1){v=7;break}c[n>>2]=1}c[s>>2]=(c[s>>2]|0)+1}if((v|0)==7){Ca(2952,2368,1244,2968)}c[h>>2]=c[n>>2];u=c[h>>2]|0;i=g;return u|0}function Uf(b){b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0;d=i;i=i+32|0;e=d+16|0;f=d+12|0;g=d+8|0;h=d+4|0;j=d;c[f>>2]=b;c[g>>2]=Ch(c[c[f>>2]>>2]|0,95)|0;if((c[g>>2]|0)!=0){c[j>>2]=(c[g>>2]|0)-(c[c[f>>2]>>2]|0);c[h>>2]=_f((c[j>>2]|0)+1|0)|0;Qh(c[h>>2]|0,c[c[f>>2]>>2]|0,c[j>>2]|0)|0;a[(c[h>>2]|0)+(c[j>>2]|0)|0]=0;c[c[f>>2]>>2]=(c[g>>2]|0)+1;c[e>>2]=c[h>>2];k=c[e>>2]|0;i=d;return k|0}else{c[e>>2]=0;k=c[e>>2]|0;i=d;return k|0}return 0}function Vf(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;b=Oc(c[2264+(c[(c[e>>2]|0)+12>>2]<<2)>>2]|0,c[c[e>>2]>>2]|0,c[(c[e>>2]|0)+4>>2]|0,c[f>>2]|0)|0;i=d;return b|0}function Wf(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;e=i;i=i+48|0;f=e+40|0;g=e+36|0;h=e+32|0;j=e+28|0;k=e+24|0;l=e+20|0;m=e+16|0;n=e+12|0;o=e+8|0;p=e+4|0;q=e;c[f>>2]=b;c[g>>2]=d;c[h>>2]=c[(c[f>>2]|0)+4>>2];c[j>>2]=c[c[f>>2]>>2];c[k>>2]=_f(c[c[j>>2]>>2]|0)|0;re(c[j>>2]|0,c[k>>2]|0,c[g>>2]|0,0,0);Oh(c[h>>2]|0,0,c[c[j>>2]>>2]|0)|0;c[l>>2]=0;while(1){if((c[l>>2]|0)>=(c[(c[j>>2]|0)+8>>2]|0)){r=17;break}c[m>>2]=(c[(c[j>>2]|0)+12>>2]|0)+(c[l>>2]<<4);c[n>>2]=c[(c[m>>2]|0)+8>>2];c[o>>2]=c[(c[m>>2]|0)+12>>2];if((c[n>>2]|0)==0){s=2}else{s=a[(c[k>>2]|0)+(((c[n>>2]|0)-(c[(c[j>>2]|0)+4>>2]|0)|0)/24|0)|0]|0}c[p>>2]=s;if((c[o>>2]|0)==0){t=2}else{t=a[(c[k>>2]|0)+(((c[o>>2]|0)-(c[(c[j>>2]|0)+4>>2]|0)|0)/24|0)|0]|0}c[q>>2]=t;if((c[p>>2]|0)==1){r=8;break}if((c[q>>2]|0)==1){r=10;break}if((c[p>>2]|0)!=(c[q>>2]|0)){if((c[n>>2]|0)!=0){g=(c[h>>2]|0)+(((c[n>>2]|0)-(c[(c[j>>2]|0)+4>>2]|0)|0)/24|0)|0;a[g]=(a[g]|0)+1<<24>>24}if((c[o>>2]|0)!=0){g=(c[h>>2]|0)+(((c[o>>2]|0)-(c[(c[j>>2]|0)+4>>2]|0)|0)/24|0)|0;a[g]=(a[g]|0)+1<<24>>24}}c[l>>2]=(c[l>>2]|0)+1}if((r|0)==8){Ca(3288,2368,1302,3304)}else if((r|0)==10){Ca(3320,2368,1303,3304)}else if((r|0)==17){$f(c[k>>2]|0);i=e;return}}function Xf(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0;d=i;i=i+32|0;e=d+16|0;f=d+12|0;g=d+8|0;h=d+4|0;j=d;c[e>>2]=a;c[f>>2]=b;c[j>>2]=uf(c[e>>2]|0,c[f>>2]|0)|0;c[h>>2]=vf(c[j>>2]|0)|0;if((c[(c[h>>2]|0)+4>>2]|0)!=1){c[g>>2]=(c[(c[h>>2]|0)+4>>2]|0)==0;xf(c[h>>2]|0);xf(c[j>>2]|0);i=d;return c[g>>2]|0}else{Ca(3216,2368,1321,3264)}return 0}function Yf(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;f=i;i=i+32|0;g=f+28|0;h=f+24|0;j=f+20|0;k=f+16|0;l=f+12|0;m=f+8|0;n=f+4|0;o=f;c[g>>2]=b;c[h>>2]=d;c[j>>2]=e;c[l>>2]=c[c[c[g>>2]>>2]>>2];c[m>>2]=Ke(c[g>>2]|0)|0;c[k>>2]=_f(c[l>>2]<<2)|0;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[l>>2]|0)){break}c[(c[k>>2]|0)+(c[o>>2]<<2)>>2]=c[o>>2];c[o>>2]=(c[o>>2]|0)+1}Mg(c[k>>2]|0,c[l>>2]|0,4,c[h>>2]|0);c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[l>>2]|0)){break}c[n>>2]=Ke(c[m>>2]|0)|0;a[(c[(c[m>>2]|0)+4>>2]|0)+(c[(c[k>>2]|0)+(c[o>>2]<<2)>>2]|0)|0]=-1;if((Xf(c[m>>2]|0,c[j>>2]|0)|0)!=0){Le(c[n>>2]|0)}else{Le(c[m>>2]|0);c[m>>2]=c[n>>2]}c[o>>2]=(c[o>>2]|0)+1}$f(c[k>>2]|0);i=f;return c[m>>2]|0}function Zf(b){b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;d=i;i=i+48|0;e=d;f=d+32|0;g=d+28|0;h=d+24|0;j=d+20|0;k=d+16|0;l=d+12|0;m=d+8|0;n=d+4|0;c[f>>2]=b;c[g>>2]=c[c[f>>2]>>2];c[j>>2]=c[c[g>>2]>>2];c[k>>2]=_f((c[j>>2]|0)+1|0)|0;c[l>>2]=c[k>>2];c[m>>2]=0;c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[j>>2]|0)){break}g=c[m>>2]|0;if((a[(c[(c[f>>2]|0)+4>>2]|0)+(c[n>>2]|0)|0]|0)<0){if((g|0)>25){b=c[l>>2]|0;c[e>>2]=(c[m>>2]|0)+97-1;o=cb(b|0,3208,e|0)|0;c[l>>2]=(c[l>>2]|0)+o;c[m>>2]=0}c[m>>2]=(c[m>>2]|0)+1}else{if((g|0)!=0){g=c[l>>2]|0;c[e>>2]=(c[m>>2]|0)+97-1;o=cb(g|0,3208,e|0)|0;c[l>>2]=(c[l>>2]|0)+o;c[m>>2]=0}o=c[l>>2]|0;do{if((a[(c[(c[f>>2]|0)+4>>2]|0)+(c[n>>2]|0)|0]|0)>=0){g=a[(c[(c[f>>2]|0)+4>>2]|0)+(c[n>>2]|0)|0]|0;if((a[(c[(c[f>>2]|0)+4>>2]|0)+(c[n>>2]|0)|0]|0)<10){p=g+48|0;break}else{p=g-10+65|0;break}}else{p=32}}while(0);c[e>>2]=p;g=cb(o|0,3208,e|0)|0;c[l>>2]=(c[l>>2]|0)+g}c[n>>2]=(c[n>>2]|0)+1}if((c[m>>2]|0)==0){q=c[k>>2]|0;r=bg(q)|0;c[h>>2]=r;s=c[k>>2]|0;$f(s);t=c[h>>2]|0;i=d;return t|0}n=c[l>>2]|0;c[e>>2]=(c[m>>2]|0)+97-1;m=cb(n|0,3208,e|0)|0;c[l>>2]=(c[l>>2]|0)+m;q=c[k>>2]|0;r=bg(q)|0;c[h>>2]=r;s=c[k>>2]|0;$f(s);t=c[h>>2]|0;i=d;return t|0}function _f(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+8|0;e=b+4|0;c[d>>2]=a;c[e>>2]=Fh(c[d>>2]|0)|0;if((c[e>>2]|0)!=0){f=c[e>>2]|0;i=b;return f|0}Ed(4896,b);f=c[e>>2]|0;i=b;return f|0}function $f(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[d>>2]|0)==0){i=b;return}Gh(c[d>>2]|0);i=b;return}function ag(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0;d=i;i=i+16|0;e=d+12|0;f=d+8|0;g=d+4|0;c[e>>2]=a;c[f>>2]=b;if((c[e>>2]|0)!=0){c[g>>2]=Hh(c[e>>2]|0,c[f>>2]|0)|0}else{c[g>>2]=Fh(c[f>>2]|0)|0}if((c[g>>2]|0)!=0){h=c[g>>2]|0;i=d;return h|0}Ed(4896,d);h=c[g>>2]|0;i=d;return h|0}function bg(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;c[e>>2]=_f(1+(Nh(c[d>>2]|0)|0)|0)|0;Rh(c[e>>2]|0,c[d>>2]|0)|0;i=b;return c[e>>2]|0}function cg(b){b=b|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;e=i;i=i+112|0;f=e;g=e+20|0;h=e+24|0;j=e+16|0;k=e+12|0;l=e+8|0;m=e+4|0;c[g>>2]=b;c[(c[g>>2]|0)+128>>2]=c[(c[(c[g>>2]|0)+8>>2]|0)+120>>2];c[f>>2]=c[c[(c[g>>2]|0)+8>>2]>>2];cb(h|0,4912,f|0)|0;c[l>>2]=0;c[k>>2]=0;while(1){if((a[h+(c[k>>2]|0)|0]|0)==0){break}if(($a(d[h+(c[k>>2]|0)|0]|0)|0)==0){b=(fb(d[h+(c[k>>2]|0)|0]|0)|0)&255;n=c[l>>2]|0;c[l>>2]=n+1;a[h+n|0]=b}c[k>>2]=(c[k>>2]|0)+1}a[h+(c[l>>2]|0)|0]=0;l=bb(h|0)|0;c[j>>2]=l;if((l|0)==0){i=e;return}l=c[j>>2]|0;c[f>>2]=m;j=(Ka(l|0,4928,f|0)|0)==1;if(!(j&(c[m>>2]|0)>0)){i=e;return}c[(c[g>>2]|0)+128>>2]=c[m>>2];i=e;return}function dg(b,e,f,h){b=b|0;e=e|0;f=f|0;h=h|0;var j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;j=i;i=i+128|0;k=j;l=j+40|0;m=j+36|0;n=j+32|0;o=j+28|0;p=j+24|0;q=j+20|0;r=j+16|0;s=j+48|0;t=j+12|0;u=j+8|0;v=j+4|0;c[l>>2]=b;c[m>>2]=e;c[n>>2]=f;c[o>>2]=h;c[p>>2]=_f(152)|0;Dd(q,r);c[c[p>>2]>>2]=c[l>>2];c[(c[p>>2]|0)+8>>2]=c[m>>2];l=hh(c[q>>2]|0,c[r>>2]|0)|0;c[(c[p>>2]|0)+4>>2]=l;c[(c[p>>2]|0)+60>>2]=0;c[(c[p>>2]|0)+56>>2]=0;c[(c[p>>2]|0)+52>>2]=0;c[(c[p>>2]|0)+64>>2]=0;l=Fb[c[(c[m>>2]|0)+12>>2]&1]()|0;c[(c[p>>2]|0)+68>>2]=l;c[(c[p>>2]|0)+144>>2]=0;c[(c[p>>2]|0)+148>>2]=0;c[k>>2]=c[c[(c[p>>2]|0)+8>>2]>>2];cb(s|0,4936,k|0)|0;c[v>>2]=0;c[u>>2]=0;while(1){if((a[s+(c[u>>2]|0)|0]|0)==0){break}if(($a(d[s+(c[u>>2]|0)|0]|0)|0)==0){k=(fb(d[s+(c[u>>2]|0)|0]|0)|0)&255;l=c[v>>2]|0;c[v>>2]=l+1;a[s+l|0]=k}c[u>>2]=(c[u>>2]|0)+1}a[s+(c[v>>2]|0)|0]=0;v=bb(s|0)|0;c[t>>2]=v;if((v|0)!=0){Hb[c[(c[(c[p>>2]|0)+8>>2]|0)+20>>2]&7](c[(c[p>>2]|0)+68>>2]|0,c[t>>2]|0)}c[(c[p>>2]|0)+72>>2]=0;c[(c[p>>2]|0)+36>>2]=0;c[(c[p>>2]|0)+32>>2]=0;c[(c[p>>2]|0)+40>>2]=0;c[(c[p>>2]|0)+44>>2]=0;c[(c[p>>2]|0)+48>>2]=2;c[(c[p>>2]|0)+76>>2]=0;c[(c[p>>2]|0)+84>>2]=0;c[(c[p>>2]|0)+12>>2]=0;c[(c[p>>2]|0)+16>>2]=0;c[(c[p>>2]|0)+20>>2]=0;c[(c[p>>2]|0)+28>>2]=0;c[(c[p>>2]|0)+24>>2]=0;g[(c[p>>2]|0)+92>>2]=0.0;g[(c[p>>2]|0)+88>>2]=0.0;g[(c[p>>2]|0)+100>>2]=0.0;g[(c[p>>2]|0)+96>>2]=0.0;c[(c[p>>2]|0)+104>>2]=0;c[(c[p>>2]|0)+80>>2]=0;c[(c[p>>2]|0)+124>>2]=0;c[(c[p>>2]|0)+116>>2]=0;c[(c[p>>2]|0)+108>>2]=0;g[(c[p>>2]|0)+112>>2]=0.0;c[(c[p>>2]|0)+140>>2]=0;c[(c[p>>2]|0)+136>>2]=0;c[(c[p>>2]|0)+132>>2]=0;if((c[n>>2]|0)!=0){t=hc(c[n>>2]|0,c[p>>2]|0,c[o>>2]|0)|0;c[(c[p>>2]|0)+120>>2]=t;w=c[p>>2]|0;cg(w);x=c[q>>2]|0;$f(x);y=c[p>>2]|0;i=j;return y|0}else{c[(c[p>>2]|0)+120>>2]=0;w=c[p>>2]|0;cg(w);x=c[q>>2]|0;$f(x);y=c[p>>2]|0;i=j;return y|0}return 0}function eg(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b;c[d>>2]=a;while(1){e=c[d>>2]|0;if((c[(c[d>>2]|0)+52>>2]|0)<=0){break}a=e+52|0;c[a>>2]=(c[a>>2]|0)+ -1;Gb[c[(c[(c[d>>2]|0)+8>>2]|0)+68>>2]&7](c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)>>2]|0);$f(c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)+4>>2]|0)}if((c[e+76>>2]|0)==0){i=b;return}Hb[c[(c[(c[d>>2]|0)+8>>2]|0)+140>>2]&7](c[(c[d>>2]|0)+120>>2]|0,c[(c[d>>2]|0)+76>>2]|0);i=b;return}function fg(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;f=i;i=i+48|0;g=f+32|0;h=f+28|0;j=f+24|0;k=f+20|0;l=f+16|0;m=f+12|0;n=f+8|0;o=f+4|0;p=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;if((c[(c[g>>2]|0)+76>>2]|0)!=0?(c[(c[g>>2]|0)+132>>2]|0)>0:0){Hb[c[(c[(c[g>>2]|0)+8>>2]|0)+140>>2]&7](c[(c[g>>2]|0)+120>>2]|0,c[(c[g>>2]|0)+76>>2]|0);e=Qb[c[(c[(c[g>>2]|0)+8>>2]|0)+136>>2]&15](c[(c[g>>2]|0)+120>>2]|0,c[c[(c[g>>2]|0)+64>>2]>>2]|0)|0;c[(c[g>>2]|0)+76>>2]=e}a:do{if((c[k>>2]|0)!=0){c[m>>2]=1;do{c[m>>2]=c[m>>2]<<1;Sb[c[(c[(c[g>>2]|0)+8>>2]|0)+124>>2]&7](c[(c[g>>2]|0)+68>>2]|0,c[m>>2]|0,n,o);if((c[n>>2]|0)>(c[c[h>>2]>>2]|0)){break a}}while((c[o>>2]|0)<=(c[c[j>>2]>>2]|0))}else{c[m>>2]=(c[(c[g>>2]|0)+128>>2]|0)+1}}while(0);c[l>>2]=1;while(1){if(((c[m>>2]|0)-(c[l>>2]|0)|0)<=1){break}c[p>>2]=((c[m>>2]|0)+(c[l>>2]|0)|0)/2|0;Sb[c[(c[(c[g>>2]|0)+8>>2]|0)+124>>2]&7](c[(c[g>>2]|0)+68>>2]|0,c[p>>2]|0,n,o);if((c[n>>2]|0)<=(c[c[h>>2]>>2]|0)?(c[o>>2]|0)<=(c[c[j>>2]>>2]|0):0){c[l>>2]=c[p>>2];continue}c[m>>2]=c[p>>2]}c[(c[g>>2]|0)+132>>2]=c[l>>2];if((c[k>>2]|0)==0){q=c[g>>2]|0;gg(q);r=c[g>>2]|0;s=r+136|0;t=c[s>>2]|0;u=c[h>>2]|0;c[u>>2]=t;v=c[g>>2]|0;w=v+140|0;x=c[w>>2]|0;y=c[j>>2]|0;c[y>>2]=x;i=f;return}c[(c[g>>2]|0)+128>>2]=c[(c[g>>2]|0)+132>>2];q=c[g>>2]|0;gg(q);r=c[g>>2]|0;s=r+136|0;t=c[s>>2]|0;u=c[h>>2]|0;c[u>>2]=t;v=c[g>>2]|0;w=v+140|0;x=c[w>>2]|0;y=c[j>>2]|0;c[y>>2]=x;i=f;return}function gg(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[(c[d>>2]|0)+132>>2]|0)<=0){i=b;return}Sb[c[(c[(c[d>>2]|0)+8>>2]|0)+124>>2]&7](c[(c[d>>2]|0)+68>>2]|0,c[(c[d>>2]|0)+132>>2]|0,(c[d>>2]|0)+136|0,(c[d>>2]|0)+140|0);Sb[c[(c[(c[d>>2]|0)+8>>2]|0)+128>>2]&7](c[(c[d>>2]|0)+120>>2]|0,c[(c[d>>2]|0)+76>>2]|0,c[(c[d>>2]|0)+68>>2]|0,c[(c[d>>2]|0)+132>>2]|0);i=b;return}function hg(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;Gb[c[(c[(c[e>>2]|0)+8>>2]|0)+28>>2]&7](c[(c[e>>2]|0)+68>>2]|0);b=Lb[c[(c[(c[e>>2]|0)+8>>2]|0)+32>>2]&15](c[f>>2]|0)|0;c[(c[e>>2]|0)+68>>2]=b;i=d;return}function ig(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[(c[d>>2]|0)+76>>2]|0)!=0){Hb[c[(c[(c[d>>2]|0)+8>>2]|0)+140>>2]&7](c[(c[d>>2]|0)+120>>2]|0,c[(c[d>>2]|0)+76>>2]|0)}a=Qb[c[(c[(c[d>>2]|0)+8>>2]|0)+136>>2]&15](c[(c[d>>2]|0)+120>>2]|0,c[c[(c[d>>2]|0)+64>>2]>>2]|0)|0;c[(c[d>>2]|0)+76>>2]=a;gg(c[d>>2]|0);jg(c[d>>2]|0);i=b;return}function jg(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[(c[d>>2]|0)+120>>2]|0)==0){Ca(5080,4976,834,5096)}if((c[(c[d>>2]|0)+60>>2]|0)<=0){i=b;return}if((c[(c[d>>2]|0)+76>>2]|0)==0){i=b;return}rc(c[(c[d>>2]|0)+120>>2]|0);do{if(((c[(c[d>>2]|0)+84>>2]|0)!=0?+g[(c[d>>2]|0)+88>>2]>0.0:0)?+g[(c[d>>2]|0)+92>>2]<+g[(c[d>>2]|0)+88>>2]:0){if((c[(c[d>>2]|0)+104>>2]|0)!=0){Kb[c[(c[(c[d>>2]|0)+8>>2]|0)+144>>2]&1](c[(c[d>>2]|0)+120>>2]|0,c[(c[d>>2]|0)+76>>2]|0,c[(c[d>>2]|0)+84>>2]|0,c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[d>>2]|0)+104>>2]|0,c[(c[d>>2]|0)+80>>2]|0,+g[(c[d>>2]|0)+92>>2],+g[(c[d>>2]|0)+100>>2]);break}else{Ca(5112,4976,840,5096)}}else{e=11}}while(0);if((e|0)==11){Kb[c[(c[(c[d>>2]|0)+8>>2]|0)+144>>2]&1](c[(c[d>>2]|0)+120>>2]|0,c[(c[d>>2]|0)+76>>2]|0,0,c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,1,c[(c[d>>2]|0)+80>>2]|0,0.0,+g[(c[d>>2]|0)+100>>2])}sc(c[(c[d>>2]|0)+120>>2]|0);i=b;return}function kg(b){b=b|0;var d=0,e=0,f=0,h=0,j=0,k=0,l=0,m=0,n=0;d=i;i=i+48|0;e=d+20|0;f=d+16|0;h=d+24|0;j=d+12|0;k=d+8|0;l=d+4|0;m=d;c[e>>2]=b;lg(c[e>>2]|0);eg(c[e>>2]|0);if((c[(c[e>>2]|0)+52>>2]|0)!=0){Ca(4952,4976,361,4992)}b=(c[e>>2]|0)+48|0;if((c[(c[e>>2]|0)+48>>2]|0)==1){c[b>>2]=2}else{if((c[b>>2]|0)==0){c[(c[e>>2]|0)+48>>2]=2}else{a[h+15|0]=0;a[h]=49+(((jh(c[(c[e>>2]|0)+4>>2]|0,9)|0)&255)<<24>>24);c[j>>2]=1;while(1){n=c[e>>2]|0;if((c[j>>2]|0)>=15){break}b=48+(((jh(c[n+4>>2]|0,10)|0)&255)<<24>>24)&255;a[h+(c[j>>2]|0)|0]=b;c[j>>2]=(c[j>>2]|0)+1}$f(c[n+40>>2]|0);n=bg(h)|0;c[(c[e>>2]|0)+40>>2]=n;if((c[(c[e>>2]|0)+72>>2]|0)!=0){Gb[c[(c[(c[e>>2]|0)+8>>2]|0)+28>>2]&7](c[(c[e>>2]|0)+72>>2]|0)}n=Lb[c[(c[(c[e>>2]|0)+8>>2]|0)+32>>2]&15](c[(c[e>>2]|0)+68>>2]|0)|0;c[(c[e>>2]|0)+72>>2]=n}$f(c[(c[e>>2]|0)+32>>2]|0);$f(c[(c[e>>2]|0)+36>>2]|0);$f(c[(c[e>>2]|0)+44>>2]|0);c[(c[e>>2]|0)+44>>2]=0;n=c[(c[e>>2]|0)+40>>2]|0;c[f>>2]=hh(n,Nh(c[(c[e>>2]|0)+40>>2]|0)|0)|0;n=Db[c[(c[(c[e>>2]|0)+8>>2]|0)+52>>2]&3](c[(c[e>>2]|0)+72>>2]|0,c[f>>2]|0,(c[e>>2]|0)+44|0,(c[(c[e>>2]|0)+120>>2]|0)!=0|0)|0;c[(c[e>>2]|0)+32>>2]=n;c[(c[e>>2]|0)+36>>2]=0;kh(c[f>>2]|0)}if((c[(c[e>>2]|0)+52>>2]|0)>=(c[(c[e>>2]|0)+56>>2]|0)){c[(c[e>>2]|0)+56>>2]=(c[(c[e>>2]|0)+52>>2]|0)+128;f=ag(c[(c[e>>2]|0)+64>>2]|0,(c[(c[e>>2]|0)+56>>2]|0)*12|0)|0;c[(c[e>>2]|0)+64>>2]=f}f=Mb[c[(c[(c[e>>2]|0)+8>>2]|0)+60>>2]&31](c[e>>2]|0,c[(c[e>>2]|0)+68>>2]|0,c[(c[e>>2]|0)+32>>2]|0)|0;c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+52>>2]|0)*12|0)>>2]=f;do{if((c[(c[(c[e>>2]|0)+8>>2]|0)+72>>2]|0)!=0?(c[(c[e>>2]|0)+44>>2]|0)!=0:0){c[l>>2]=0;c[m>>2]=Db[c[(c[(c[e>>2]|0)+8>>2]|0)+76>>2]&3](c[c[(c[e>>2]|0)+64>>2]>>2]|0,c[c[(c[e>>2]|0)+64>>2]>>2]|0,c[(c[e>>2]|0)+44>>2]|0,l)|0;if((c[m>>2]|0)==0){Ca(5008,4976,442,4992)}if((c[l>>2]|0)!=0){Ca(5008,4976,442,4992)}c[k>>2]=Qb[c[(c[(c[e>>2]|0)+8>>2]|0)+116>>2]&15](c[c[(c[e>>2]|0)+64>>2]>>2]|0,c[m>>2]|0)|0;if((c[k>>2]|0)!=0){Gb[c[(c[(c[e>>2]|0)+8>>2]|0)+68>>2]&7](c[k>>2]|0);$f(c[m>>2]|0);break}else{Ca(5024,4976,444,4992)}}}while(0);c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+52>>2]|0)*12|0)+4>>2]=0;c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+52>>2]|0)*12|0)+8>>2]=0;m=(c[e>>2]|0)+52|0;c[m>>2]=(c[m>>2]|0)+1;c[(c[e>>2]|0)+60>>2]=1;m=Qb[c[(c[(c[e>>2]|0)+8>>2]|0)+136>>2]&15](c[(c[e>>2]|0)+120>>2]|0,c[c[(c[e>>2]|0)+64>>2]>>2]|0)|0;c[(c[e>>2]|0)+76>>2]=m;gg(c[e>>2]|0);g[(c[e>>2]|0)+112>>2]=0.0;g[(c[e>>2]|0)+96>>2]=0.0;g[(c[e>>2]|0)+100>>2]=0.0;g[(c[e>>2]|0)+88>>2]=0.0;g[(c[e>>2]|0)+92>>2]=0.0;if((c[(c[e>>2]|0)+80>>2]|0)!=0){Gb[c[(c[(c[e>>2]|0)+8>>2]|0)+96>>2]&7](c[(c[e>>2]|0)+80>>2]|0)}m=Lb[c[(c[(c[e>>2]|0)+8>>2]|0)+92>>2]&15](c[c[(c[e>>2]|0)+64>>2]>>2]|0)|0;c[(c[e>>2]|0)+80>>2]=m;mg(c[e>>2]|0);c[(c[e>>2]|0)+124>>2]=0;if((c[(c[e>>2]|0)+144>>2]|0)==0){i=d;return}Gb[c[(c[e>>2]|0)+144>>2]&7](c[(c[e>>2]|0)+148>>2]|0);i=d;return}function lg(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[(c[d>>2]|0)+84>>2]|0)==0?!(+g[(c[d>>2]|0)+88>>2]!=0.0):0){i=b;return}pg(c[d>>2]|0);jg(c[d>>2]|0);i=b;return}function mg(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[(c[(c[d>>2]|0)+8>>2]|0)+180>>2]|0)!=0){e=(Qb[c[(c[(c[d>>2]|0)+8>>2]|0)+184>>2]&15](c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[d>>2]|0)+80>>2]|0)|0)!=0}else{e=0}c[(c[d>>2]|0)+108>>2]=e&1;if(((c[(c[d>>2]|0)+108>>2]|0)==0?!(+g[(c[d>>2]|0)+96>>2]!=0.0):0)?!(+g[(c[d>>2]|0)+88>>2]!=0.0):0){Gd(c[c[d>>2]>>2]|0);i=b;return}Hd(c[c[d>>2]>>2]|0);i=b;return}function ng(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;i=b;return(c[(c[d>>2]|0)+60>>2]|0)>1|0}function og(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;i=b;return(c[(c[d>>2]|0)+60>>2]|0)<(c[(c[d>>2]|0)+52>>2]|0)|0}function pg(a){a=a|0;var b=0,d=0,e=0,f=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;if(!((c[(c[d>>2]|0)+84>>2]|0)==0?(c[(c[d>>2]|0)+60>>2]|0)<=1:0)){f=3}do{if((f|0)==3){if(!((c[(c[d>>2]|0)+104>>2]|0)>0?(c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-1|0)*12|0)+8>>2]|0)==1:0)){if((c[(c[d>>2]|0)+104>>2]|0)>=0){break}if((c[(c[d>>2]|0)+60>>2]|0)>=(c[(c[d>>2]|0)+52>>2]|0)){break}if((c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+60>>2]|0)*12|0)+8>>2]|0)!=1){break}}a=c[d>>2]|0;if((c[(c[d>>2]|0)+84>>2]|0)!=0){h=c[a+84>>2]|0}else{h=c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[a+60>>2]|0)-2|0)*12|0)>>2]|0}if((c[(c[d>>2]|0)+84>>2]|0)!=0){j=c[(c[d>>2]|0)+104>>2]|0}else{j=1}g[e>>2]=+Rb[c[(c[(c[d>>2]|0)+8>>2]|0)+152>>2]&3](h,c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,j,c[(c[d>>2]|0)+80>>2]|0);if(+g[e>>2]>0.0){g[(c[d>>2]|0)+100>>2]=0.0;g[(c[d>>2]|0)+96>>2]=+g[e>>2]}}}while(0);if((c[(c[d>>2]|0)+84>>2]|0)==0){k=c[d>>2]|0;l=k+84|0;c[l>>2]=0;m=c[d>>2]|0;n=m+88|0;g[n>>2]=0.0;o=c[d>>2]|0;p=o+92|0;g[p>>2]=0.0;q=c[d>>2]|0;r=q+104|0;c[r>>2]=0;s=c[d>>2]|0;mg(s);i=b;return}Gb[c[(c[(c[d>>2]|0)+8>>2]|0)+68>>2]&7](c[(c[d>>2]|0)+84>>2]|0);k=c[d>>2]|0;l=k+84|0;c[l>>2]=0;m=c[d>>2]|0;n=m+88|0;g[n>>2]=0.0;o=c[d>>2]|0;p=o+92|0;g[p>>2]=0.0;q=c[d>>2]|0;r=q+104|0;c[r>>2]=0;s=c[d>>2]|0;mg(s);i=b;return}function qg(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;if((c[(c[d>>2]|0)+60>>2]|0)<1){Ca(5032,4976,552,5056)}if((c[(c[d>>2]|0)+60>>2]|0)==1){i=b;return}c[e>>2]=Mb[c[(c[(c[d>>2]|0)+8>>2]|0)+60>>2]&31](c[d>>2]|0,c[(c[d>>2]|0)+68>>2]|0,c[(c[d>>2]|0)+32>>2]|0)|0;lg(c[d>>2]|0);rg(c[d>>2]|0);if((c[(c[d>>2]|0)+52>>2]|0)>=(c[(c[d>>2]|0)+56>>2]|0)){c[(c[d>>2]|0)+56>>2]=(c[(c[d>>2]|0)+52>>2]|0)+128;a=ag(c[(c[d>>2]|0)+64>>2]|0,(c[(c[d>>2]|0)+56>>2]|0)*12|0)|0;c[(c[d>>2]|0)+64>>2]=a}c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)>>2]=c[e>>2];e=bg(c[(c[d>>2]|0)+32>>2]|0)|0;c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)+4>>2]=e;c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)+8>>2]=3;e=(c[d>>2]|0)+52|0;a=(c[e>>2]|0)+1|0;c[e>>2]=a;c[(c[d>>2]|0)+60>>2]=a;if((c[(c[d>>2]|0)+80>>2]|0)!=0){Nb[c[(c[(c[d>>2]|0)+8>>2]|0)+108>>2]&3](c[(c[d>>2]|0)+80>>2]|0,c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-2|0)*12|0)>>2]|0,c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0)}g[(c[d>>2]|0)+96>>2]=0.0;g[(c[d>>2]|0)+100>>2]=0.0;pg(c[d>>2]|0);jg(c[d>>2]|0);mg(c[d>>2]|0);i=b;return}function rg(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b;c[d>>2]=a;while(1){if((c[(c[d>>2]|0)+52>>2]|0)<=(c[(c[d>>2]|0)+60>>2]|0)){break}a=c[(c[(c[d>>2]|0)+8>>2]|0)+68>>2]|0;e=(c[d>>2]|0)+52|0;f=(c[e>>2]|0)+ -1|0;c[e>>2]=f;Gb[a&7](c[(c[(c[d>>2]|0)+64>>2]|0)+(f*12|0)>>2]|0);if((c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)+4>>2]|0)==0){continue}$f(c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)+4>>2]|0)}i=b;return}function sg(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0;f=i;i=i+32|0;g=f+20|0;h=f+16|0;j=f+12|0;k=f+8|0;l=f+4|0;m=f;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=1;if(!(((c[l>>2]|0)-515|0)>>>0<=2)?!(((c[l>>2]|0)-518|0)>>>0<=2):0){if(((c[l>>2]|0)-512|0)>>>0<=2?(c[(c[h>>2]|0)+124>>2]|0)!=0:0){e=c[m>>2]|0;if((c[(c[(c[h>>2]|0)+8>>2]|0)+188>>2]&1<<(((c[(c[h>>2]|0)+124>>2]|0)-512|0)*3|0)+(c[l>>2]|0)-512|0)!=0){c[g>>2]=e;n=c[g>>2]|0;i=f;return n|0}if((e|0)!=0){o=(tg(c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,(c[(c[h>>2]|0)+124>>2]|0)+6|0)|0)!=0}else{o=0}c[m>>2]=o&1}}else{p=3}do{if((p|0)==3){if((c[(c[h>>2]|0)+124>>2]|0)==0){c[g>>2]=c[m>>2];n=c[g>>2]|0;i=f;return n|0}o=c[(c[h>>2]|0)+124>>2]|0;if(((c[l>>2]|0)-515|0)>>>0<=2){c[l>>2]=o+3;break}else{c[l>>2]=o+6;break}}}while(0);if((c[l>>2]|0)==10|(c[l>>2]|0)==13){c[l>>2]=525}if((c[l>>2]|0)==32){c[l>>2]=526}if((c[l>>2]|0)==127){c[l>>2]=8}if((c[m>>2]|0)!=0){q=(tg(c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0)|0)!=0}else{q=0}c[m>>2]=q&1;if(!(((c[l>>2]|0)-518|0)>>>0<=2)){if(((c[l>>2]|0)-512|0)>>>0<=2){c[(c[h>>2]|0)+124>>2]=c[l>>2]}}else{c[(c[h>>2]|0)+124>>2]=0}c[g>>2]=c[m>>2];n=c[g>>2]|0;i=f;return n|0}function tg(b,d,e,f){b=b|0;d=d|0;e=e|0;f=f|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0;h=i;i=i+48|0;j=h+40|0;k=h+36|0;l=h+32|0;m=h+28|0;n=h+24|0;o=h+20|0;p=h+16|0;q=h+12|0;r=h+8|0;s=h+4|0;t=h;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=Lb[c[(c[(c[j>>2]|0)+8>>2]|0)+64>>2]&15](c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0)|0;c[o>>2]=1;c[p>>2]=0;c[q>>2]=1;c[t>>2]=Ib[c[(c[(c[j>>2]|0)+8>>2]|0)+112>>2]&1](c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[j>>2]|0)+80>>2]|0,c[(c[j>>2]|0)+76>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0)|0;do{if((c[t>>2]|0)!=0){l=c[j>>2]|0;do{if((a[c[t>>2]|0]|0)!=0){c[s>>2]=Qb[c[(c[l+8>>2]|0)+116>>2]&15](c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[t>>2]|0)|0;if((c[s>>2]|0)!=0){break}else{Ca(5616,4976,629,5632)}}else{c[s>>2]=c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[l+60>>2]|0)-1|0)*12|0)>>2]}}while(0);if((c[s>>2]|0)==(c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0)){jg(c[j>>2]|0);mg(c[j>>2]|0);break}if((c[s>>2]|0)!=0){lg(c[j>>2]|0);rg(c[j>>2]|0);if((c[(c[j>>2]|0)+52>>2]|0)>=(c[(c[j>>2]|0)+56>>2]|0)){c[(c[j>>2]|0)+56>>2]=(c[(c[j>>2]|0)+52>>2]|0)+128;l=ag(c[(c[j>>2]|0)+64>>2]|0,(c[(c[j>>2]|0)+56>>2]|0)*12|0)|0;c[(c[j>>2]|0)+64>>2]=l}if((c[t>>2]|0)==0){Ca(5664,4976,645,5632)}c[(c[(c[j>>2]|0)+64>>2]|0)+((c[(c[j>>2]|0)+52>>2]|0)*12|0)>>2]=c[s>>2];c[(c[(c[j>>2]|0)+64>>2]|0)+((c[(c[j>>2]|0)+52>>2]|0)*12|0)+4>>2]=c[t>>2];c[(c[(c[j>>2]|0)+64>>2]|0)+((c[(c[j>>2]|0)+52>>2]|0)*12|0)+8>>2]=1;l=(c[j>>2]|0)+52|0;k=(c[l>>2]|0)+1|0;c[l>>2]=k;c[(c[j>>2]|0)+60>>2]=k;c[(c[j>>2]|0)+104>>2]=1;if((c[(c[j>>2]|0)+80>>2]|0)!=0){Nb[c[(c[(c[j>>2]|0)+8>>2]|0)+108>>2]&3](c[(c[j>>2]|0)+80>>2]|0,c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-2|0)*12|0)>>2]|0,c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0);u=27}else{u=27}}}else{if((c[m>>2]|0)==110|(c[m>>2]|0)==78|(c[m>>2]|0)==14){kg(c[j>>2]|0);jg(c[j>>2]|0);break}if((c[m>>2]|0)==117|(c[m>>2]|0)==85|(c[m>>2]|0)==26|(c[m>>2]|0)==31){lg(c[j>>2]|0);c[o>>2]=c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)+8>>2];c[p>>2]=1;if((Jg(c[j>>2]|0)|0)!=0){u=27;break}else{break}}if((c[m>>2]|0)==114|(c[m>>2]|0)==82|(c[m>>2]|0)==18|(c[m>>2]|0)==25){lg(c[j>>2]|0);if((Kg(c[j>>2]|0)|0)!=0){u=27;break}else{break}}if((c[m>>2]|0)==19?(c[(c[(c[j>>2]|0)+8>>2]|0)+72>>2]|0)!=0:0){if((Hg(c[j>>2]|0)|0)!=0){break}else{u=27;break}}if((c[m>>2]|0)==113|(c[m>>2]|0)==81|(c[m>>2]|0)==17){c[q>>2]=0}}}while(0);if((u|0)==27){if((c[p>>2]|0)==0){c[o>>2]=c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)+8>>2]}do{if((c[o>>2]|0)!=1){if((c[o>>2]|0)==2?(c[(c[(c[j>>2]|0)+8>>2]|0)+188>>2]&512|0)!=0:0){u=33;break}g[r>>2]=0.0}else{u=33}}while(0);if((u|0)==33){g[r>>2]=+Rb[c[(c[(c[j>>2]|0)+8>>2]|0)+148>>2]&3](c[n>>2]|0,c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[j>>2]|0)+104>>2]|0,c[(c[j>>2]|0)+80>>2]|0)}c[(c[j>>2]|0)+84>>2]=c[n>>2];c[n>>2]=0;if(+g[r>>2]>0.0){g[(c[j>>2]|0)+88>>2]=+g[r>>2]}else{g[(c[j>>2]|0)+88>>2]=0.0;pg(c[j>>2]|0)}g[(c[j>>2]|0)+92>>2]=0.0;jg(c[j>>2]|0);mg(c[j>>2]|0)}if((c[n>>2]|0)==0){v=c[q>>2]|0;i=h;return v|0}Gb[c[(c[(c[j>>2]|0)+8>>2]|0)+68>>2]&7](c[n>>2]|0);v=c[q>>2]|0;i=h;return v|0}function ug(a,b){a=a|0;b=+b;var d=0,e=0,f=0,h=0,j=0,k=0,l=0,m=0,n=0;d=i;i=i+16|0;e=d+12|0;f=d+8|0;h=d+4|0;j=d;c[e>>2]=a;g[f>>2]=b;if(+g[(c[e>>2]|0)+88>>2]>0.0){k=1}else{k=+g[(c[e>>2]|0)+96>>2]>0.0}c[h>>2]=k&1;k=(c[e>>2]|0)+92|0;g[k>>2]=+g[k>>2]+ +g[f>>2];if(!((!(+g[(c[e>>2]|0)+92>>2]>=+g[(c[e>>2]|0)+88>>2])?!(+g[(c[e>>2]|0)+88>>2]==0.0):0)?(c[(c[e>>2]|0)+84>>2]|0)!=0:0)){l=6}if((l|0)==6?+g[(c[e>>2]|0)+88>>2]>0.0:0){pg(c[e>>2]|0)}l=(c[e>>2]|0)+100|0;g[l>>2]=+g[l>>2]+ +g[f>>2];if(!(!(+g[(c[e>>2]|0)+100>>2]>=+g[(c[e>>2]|0)+96>>2])?!(+g[(c[e>>2]|0)+96>>2]==0.0):0)){g[(c[e>>2]|0)+96>>2]=0.0;g[(c[e>>2]|0)+100>>2]=0.0}if((c[h>>2]|0)!=0){jg(c[e>>2]|0)}if((c[(c[e>>2]|0)+108>>2]|0)==0){m=c[e>>2]|0;mg(m);i=d;return}g[j>>2]=+g[(c[e>>2]|0)+112>>2];h=(c[e>>2]|0)+112|0;g[h>>2]=+g[h>>2]+ +g[f>>2];if((~~+g[j>>2]|0)==(~~+g[(c[e>>2]|0)+112>>2]|0)){m=c[e>>2]|0;mg(m);i=d;return}if((c[(c[e>>2]|0)+116>>2]|0)!=0){n=c[(c[e>>2]|0)+116>>2]|0}else{n=5128}tc(c[(c[e>>2]|0)+120>>2]|0,n);m=c[e>>2]|0;mg(m);i=d;return}function vg(b,e){b=b|0;e=e|0;var f=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;f=i;i=i+144|0;h=f;j=f+48|0;k=f+44|0;l=f+40|0;m=f+36|0;n=f+56|0;o=f+32|0;p=f+28|0;q=f+24|0;r=f+20|0;s=f+16|0;t=f+12|0;c[j>>2]=b;c[k>>2]=e;c[l>>2]=Qb[c[(c[(c[j>>2]|0)+8>>2]|0)+132>>2]&15](c[c[j>>2]>>2]|0,c[k>>2]|0)|0;c[m>>2]=0;while(1){if((c[m>>2]|0)>=(c[c[k>>2]>>2]|0)){break}e=c[m>>2]|0;c[h>>2]=c[c[(c[j>>2]|0)+8>>2]>>2];c[h+4>>2]=e;cb(n|0,5136,h|0)|0;c[t>>2]=0;c[s>>2]=0;while(1){if((a[n+(c[s>>2]|0)|0]|0)==0){break}if(($a(d[n+(c[s>>2]|0)|0]|0)|0)==0){e=(fb(d[n+(c[s>>2]|0)|0]|0)|0)&255;b=c[t>>2]|0;c[t>>2]=b+1;a[n+b|0]=e}c[s>>2]=(c[s>>2]|0)+1}a[n+(c[t>>2]|0)|0]=0;e=bb(n|0)|0;c[o>>2]=e;if((e|0)!=0?(e=c[o>>2]|0,c[h>>2]=p,c[h+4>>2]=q,c[h+8>>2]=r,(Ka(e|0,5152,h|0)|0)==3):0){g[(c[l>>2]|0)+(((c[m>>2]|0)*3|0)+0<<2)>>2]=+((c[p>>2]|0)>>>0)/255.0;g[(c[l>>2]|0)+(((c[m>>2]|0)*3|0)+1<<2)>>2]=+((c[q>>2]|0)>>>0)/255.0;g[(c[l>>2]|0)+(((c[m>>2]|0)*3|0)+2<<2)>>2]=+((c[r>>2]|0)>>>0)/255.0}c[m>>2]=(c[m>>2]|0)+1}i=f;return c[l>>2]|0}function wg(b){b=b|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;e=i;i=i+128|0;f=e;g=e+40|0;h=e+36|0;j=e+32|0;k=e+48|0;l=e+28|0;m=e+24|0;n=e+20|0;o=e+16|0;p=e+12|0;q=e+8|0;r=e+4|0;c[g>>2]=b;a:do{if((c[(c[g>>2]|0)+24>>2]|0)==0){while(1){if((Mb[c[(c[(c[g>>2]|0)+8>>2]|0)+16>>2]&31](c[(c[g>>2]|0)+24>>2]|0,h,j)|0)==0){break a}if((c[(c[g>>2]|0)+28>>2]|0)<=(c[(c[g>>2]|0)+24>>2]|0)){c[(c[g>>2]|0)+28>>2]=(c[(c[g>>2]|0)+24>>2]|0)+10;b=ag(c[(c[g>>2]|0)+12>>2]|0,c[(c[g>>2]|0)+28>>2]<<2)|0;c[(c[g>>2]|0)+12>>2]=b;b=ag(c[(c[g>>2]|0)+16>>2]|0,c[(c[g>>2]|0)+28>>2]<<2)|0;c[(c[g>>2]|0)+16>>2]=b;b=ag(c[(c[g>>2]|0)+20>>2]|0,c[(c[g>>2]|0)+28>>2]<<2)|0;c[(c[g>>2]|0)+20>>2]=b}c[(c[(c[g>>2]|0)+12>>2]|0)+(c[(c[g>>2]|0)+24>>2]<<2)>>2]=c[j>>2];c[(c[(c[g>>2]|0)+16>>2]|0)+(c[(c[g>>2]|0)+24>>2]<<2)>>2]=c[h>>2];b=Qb[c[(c[(c[g>>2]|0)+8>>2]|0)+24>>2]&15](c[j>>2]|0,1)|0;c[(c[(c[g>>2]|0)+20>>2]|0)+(c[(c[g>>2]|0)+24>>2]<<2)>>2]=b;b=(c[g>>2]|0)+24|0;c[b>>2]=(c[b>>2]|0)+1}}}while(0);c[f>>2]=c[c[(c[g>>2]|0)+8>>2]>>2];cb(k|0,5168,f|0)|0;c[o>>2]=0;c[n>>2]=0;while(1){if((a[k+(c[n>>2]|0)|0]|0)==0){break}if(($a(d[k+(c[n>>2]|0)|0]|0)|0)==0){f=(fb(d[k+(c[n>>2]|0)|0]|0)|0)&255;j=c[o>>2]|0;c[o>>2]=j+1;a[k+j|0]=f}c[n>>2]=(c[n>>2]|0)+1}a[k+(c[o>>2]|0)|0]=0;o=bb(k|0)|0;c[l>>2]=o;if((o|0)==0){s=c[g>>2]|0;t=s+24|0;u=c[t>>2]|0;i=e;return u|0}o=bg(c[l>>2]|0)|0;c[l>>2]=o;c[m>>2]=o;while(1){if((a[c[m>>2]|0]|0)==0){break}c[p>>2]=c[m>>2];while(1){if((a[c[m>>2]|0]|0)!=0){v=(a[c[m>>2]|0]|0)!=58}else{v=0}w=c[m>>2]|0;if(!v){break}c[m>>2]=w+1}if((a[w]|0)!=0){o=c[m>>2]|0;c[m>>2]=o+1;a[o]=0}c[q>>2]=c[m>>2];while(1){if((a[c[m>>2]|0]|0)!=0){x=(a[c[m>>2]|0]|0)!=58}else{x=0}y=c[m>>2]|0;if(!x){break}c[m>>2]=y+1}if((a[y]|0)!=0){o=c[m>>2]|0;c[m>>2]=o+1;a[o]=0}c[r>>2]=Fb[c[(c[(c[g>>2]|0)+8>>2]|0)+12>>2]&1]()|0;Hb[c[(c[(c[g>>2]|0)+8>>2]|0)+20>>2]&7](c[r>>2]|0,c[q>>2]|0);o=(Qb[c[(c[(c[g>>2]|0)+8>>2]|0)+48>>2]&15](c[r>>2]|0,1)|0)!=0;k=c[g>>2]|0;if(o){Gb[c[(c[k+8>>2]|0)+28>>2]&7](c[r>>2]|0);continue}if((c[k+28>>2]|0)<=(c[(c[g>>2]|0)+24>>2]|0)){c[(c[g>>2]|0)+28>>2]=(c[(c[g>>2]|0)+24>>2]|0)+10;k=ag(c[(c[g>>2]|0)+12>>2]|0,c[(c[g>>2]|0)+28>>2]<<2)|0;c[(c[g>>2]|0)+12>>2]=k;k=ag(c[(c[g>>2]|0)+16>>2]|0,c[(c[g>>2]|0)+28>>2]<<2)|0;c[(c[g>>2]|0)+16>>2]=k;k=ag(c[(c[g>>2]|0)+20>>2]|0,c[(c[g>>2]|0)+28>>2]<<2)|0;c[(c[g>>2]|0)+20>>2]=k}c[(c[(c[g>>2]|0)+12>>2]|0)+(c[(c[g>>2]|0)+24>>2]<<2)>>2]=c[r>>2];k=bg(c[p>>2]|0)|0;c[(c[(c[g>>2]|0)+16>>2]|0)+(c[(c[g>>2]|0)+24>>2]<<2)>>2]=k;k=Qb[c[(c[(c[g>>2]|0)+8>>2]|0)+24>>2]&15](c[r>>2]|0,1)|0;c[(c[(c[g>>2]|0)+20>>2]|0)+(c[(c[g>>2]|0)+24>>2]<<2)>>2]=k;k=(c[g>>2]|0)+24|0;c[k>>2]=(c[k>>2]|0)+1}$f(c[l>>2]|0);s=c[g>>2]|0;t=s+24|0;u=c[t>>2]|0;i=e;return u|0}function xg(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0;f=i;i=i+16|0;g=f+12|0;h=f+8|0;j=f+4|0;k=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;if((c[h>>2]|0)<0){Ca(5184,4976,1021,5216)}if((c[h>>2]|0)<(c[(c[g>>2]|0)+24>>2]|0)){c[c[j>>2]>>2]=c[(c[(c[g>>2]|0)+16>>2]|0)+(c[h>>2]<<2)>>2];c[c[k>>2]>>2]=c[(c[(c[g>>2]|0)+12>>2]|0)+(c[h>>2]<<2)>>2];i=f;return}else{Ca(5184,4976,1021,5216)}}function yg(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0;b=i;i=i+16|0;d=b+12|0;e=b+8|0;f=b+4|0;g=b;c[d>>2]=a;c[e>>2]=Qb[c[(c[(c[d>>2]|0)+8>>2]|0)+24>>2]&15](c[(c[d>>2]|0)+68>>2]|0,1)|0;c[g>>2]=-1;c[f>>2]=0;while(1){if((c[f>>2]|0)>=(c[(c[d>>2]|0)+24>>2]|0)){h=6;break}a=(Lh(c[e>>2]|0,c[(c[(c[d>>2]|0)+20>>2]|0)+(c[f>>2]<<2)>>2]|0)|0)!=0;j=c[f>>2]|0;if(!a){break}c[f>>2]=j+1}if((h|0)==6){k=c[e>>2]|0;$f(k);l=c[g>>2]|0;i=b;return l|0}c[g>>2]=j;k=c[e>>2]|0;$f(k);l=c[g>>2]|0;i=b;return l|0}function zg(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;i=b;return c[(c[(c[d>>2]|0)+8>>2]|0)+176>>2]|0}function Ag(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0;e=i;i=i+16|0;f=e+8|0;g=e+4|0;h=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;c[(c[f>>2]|0)+144>>2]=c[g>>2];c[(c[f>>2]|0)+148>>2]=c[h>>2];i=e;return}function Bg(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;f=i;i=i+48|0;g=f;h=f+40|0;j=f+36|0;k=f+32|0;l=f+28|0;m=f+24|0;n=f+20|0;o=f+16|0;p=f+12|0;q=f+44|0;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;if((c[l>>2]|0)==0){Ca(5240,4976,1069,5256)}c[m>>2]=_f(40+(Nh(c[c[(c[j>>2]|0)+8>>2]>>2]|0)|0)|0)|0;e=c[k>>2]|0;if((e|0)==2|(e|0)==1){d=c[m>>2]|0;if((c[(c[j>>2]|0)+72>>2]|0)==0){$f(d);c[h>>2]=0;r=c[h>>2]|0;i=f;return r|0}b=(c[k>>2]|0)==1?5320:5328;c[g>>2]=c[c[(c[j>>2]|0)+8>>2]>>2];c[g+4>>2]=b;cb(d|0,5304,g|0)|0;c[c[l>>2]>>2]=c[m>>2];c[p>>2]=_f(32)|0;c[(c[p>>2]|0)+4>>2]=0;d=c[p>>2]|0;if((c[k>>2]|0)==1){c[d>>2]=5336}else{c[d>>2]=5360}c[(c[p>>2]|0)+12>>2]=0;c[n>>2]=Qb[c[(c[(c[j>>2]|0)+8>>2]|0)+24>>2]&15](c[(c[j>>2]|0)+72>>2]|0,(c[k>>2]|0)==1|0)|0;if((c[n>>2]|0)==0){Ca(5368,4976,1105,5256)}d=c[j>>2]|0;if((c[k>>2]|0)==2){if((c[d+32>>2]|0)!=0){s=c[(c[j>>2]|0)+32>>2]|0}else{s=5128}c[o>>2]=s;a[q]=58}else{if((c[d+40>>2]|0)!=0){t=c[(c[j>>2]|0)+40>>2]|0}else{t=5128}c[o>>2]=t;a[q]=35}t=Nh(c[n>>2]|0)|0;d=_f(t+(Nh(c[o>>2]|0)|0)+2|0)|0;c[(c[p>>2]|0)+8>>2]=d;d=c[(c[p>>2]|0)+8>>2]|0;t=a[q]|0;q=c[o>>2]|0;c[g>>2]=c[n>>2];c[g+4>>2]=t;c[g+8>>2]=q;cb(d|0,5376,g|0)|0;$f(c[n>>2]|0);c[(c[p>>2]|0)+20>>2]=3;c[(c[p>>2]|0)+24>>2]=0;c[(c[p>>2]|0)+16>>2]=0;c[(c[p>>2]|0)+28>>2]=0;c[h>>2]=c[p>>2];r=c[h>>2]|0;i=f;return r|0}else if((e|0)==0){e=c[m>>2]|0;c[g>>2]=c[c[(c[j>>2]|0)+8>>2]>>2];cb(e|0,5280,g|0)|0;c[c[l>>2]>>2]=c[m>>2];c[h>>2]=Lb[c[(c[(c[j>>2]|0)+8>>2]|0)+40>>2]&15](c[(c[j>>2]|0)+68>>2]|0)|0;r=c[h>>2]|0;i=f;return r|0}else{Ca(5384,4976,1124,5256)}return 0}function Cg(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;b=Dg(c[e>>2]|0,c[f>>2]|0,0)|0;i=d;return b|0}function Dg(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0;f=i;i=i+64|0;g=f+52|0;h=f+48|0;j=f+44|0;k=f+40|0;l=f+36|0;m=f+32|0;n=f+28|0;o=f+24|0;p=f+20|0;q=f+16|0;r=f+12|0;s=f+8|0;t=f+4|0;u=f;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[o>>2]=Ch(c[j>>2]|0,35)|0;c[n>>2]=Ch(c[j>>2]|0,58)|0;do{if((c[n>>2]|0)!=0){if((c[o>>2]|0)!=0?!((c[n>>2]|0)>>>0<(c[o>>2]|0)>>>0):0){v=5;break}e=c[n>>2]|0;c[n>>2]=e+1;a[e]=0;c[m>>2]=c[j>>2];c[o>>2]=0}else{v=5}}while(0);a:do{if((v|0)==5){do{if((c[o>>2]|0)!=0){if((c[n>>2]|0)!=0?!((c[o>>2]|0)>>>0<(c[n>>2]|0)>>>0):0){break}e=c[o>>2]|0;c[o>>2]=e+1;a[e]=0;c[m>>2]=c[j>>2];c[n>>2]=0;break a}}while(0);if((c[k>>2]|0)==1){c[o>>2]=c[j>>2];c[n>>2]=0;c[m>>2]=0;break}e=c[j>>2]|0;if((c[k>>2]|0)==2){c[n>>2]=e;c[o>>2]=0;c[m>>2]=0;break}else{c[m>>2]=e;c[n>>2]=0;c[o>>2]=0;break}}}while(0);c[s>>2]=0;c[r>>2]=0;c[q>>2]=0;c[p>>2]=0;if((c[m>>2]|0)!=0){k=c[(c[h>>2]|0)+8>>2]|0;if((c[n>>2]|0)!=0){c[p>>2]=Lb[c[k+32>>2]&15](c[(c[h>>2]|0)+68>>2]|0)|0}else{c[p>>2]=Fb[c[k+12>>2]&1]()|0}Hb[c[(c[(c[h>>2]|0)+8>>2]|0)+20>>2]&7](c[p>>2]|0,c[m>>2]|0);c[l>>2]=Qb[c[(c[(c[h>>2]|0)+8>>2]|0)+48>>2]&15](c[p>>2]|0,(c[n>>2]|0)==0|0)|0;m=c[h>>2]|0;if((c[l>>2]|0)!=0){Gb[c[(c[m+8>>2]|0)+28>>2]&7](c[p>>2]|0);c[g>>2]=c[l>>2];w=c[g>>2]|0;i=f;return w|0}c[r>>2]=c[m+72>>2];c[s>>2]=c[(c[h>>2]|0)+68>>2];if((c[o>>2]|0)==0?(c[n>>2]|0)==0:0){c[q>>2]=Lb[c[(c[(c[h>>2]|0)+8>>2]|0)+32>>2]&15](c[p>>2]|0)|0}else{c[q>>2]=Lb[c[(c[(c[h>>2]|0)+8>>2]|0)+32>>2]&15](c[(c[h>>2]|0)+68>>2]|0)|0;c[u>>2]=Qb[c[(c[(c[h>>2]|0)+8>>2]|0)+24>>2]&15](c[p>>2]|0,0)|0;Hb[c[(c[(c[h>>2]|0)+8>>2]|0)+20>>2]&7](c[q>>2]|0,c[u>>2]|0);$f(c[u>>2]|0)}c[t>>2]=1}else{c[p>>2]=c[(c[h>>2]|0)+72>>2];c[q>>2]=c[(c[h>>2]|0)+68>>2];c[t>>2]=0}if((c[n>>2]|0)!=0?(c[l>>2]=Qb[c[(c[(c[h>>2]|0)+8>>2]|0)+56>>2]&15](c[q>>2]|0,c[n>>2]|0)|0,(c[l>>2]|0)!=0):0){if((c[t>>2]|0)!=0){if((c[p>>2]|0)!=0){Gb[c[(c[(c[h>>2]|0)+8>>2]|0)+28>>2]&7](c[p>>2]|0)}if((c[q>>2]|0)!=0){Gb[c[(c[(c[h>>2]|0)+8>>2]|0)+28>>2]&7](c[q>>2]|0)}}c[g>>2]=c[l>>2];w=c[g>>2]|0;i=f;return w|0}c[(c[h>>2]|0)+68>>2]=c[q>>2];c[(c[h>>2]|0)+72>>2]=c[p>>2];if((c[r>>2]|0)!=0){Gb[c[(c[(c[h>>2]|0)+8>>2]|0)+28>>2]&7](c[r>>2]|0)}if((c[s>>2]|0)!=0){Gb[c[(c[(c[h>>2]|0)+8>>2]|0)+28>>2]&7](c[s>>2]|0)}$f(c[(c[h>>2]|0)+32>>2]|0);$f(c[(c[h>>2]|0)+36>>2]|0);c[(c[h>>2]|0)+36>>2]=0;c[(c[h>>2]|0)+32>>2]=0;$f(c[(c[h>>2]|0)+40>>2]|0);c[(c[h>>2]|0)+40>>2]=0;if((c[n>>2]|0)!=0){s=bg(c[n>>2]|0)|0;c[(c[h>>2]|0)+32>>2]=s;c[(c[h>>2]|0)+48>>2]=1;$f(c[(c[h>>2]|0)+44>>2]|0);c[(c[h>>2]|0)+44>>2]=0}if((c[o>>2]|0)!=0){s=bg(c[o>>2]|0)|0;c[(c[h>>2]|0)+40>>2]=s;c[(c[h>>2]|0)+48>>2]=0}c[g>>2]=0;w=c[g>>2]|0;i=f;return w|0}function Eg(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0;b=i;i=i+32|0;d=b;e=b+16|0;f=b+12|0;g=b+8|0;c[e>>2]=a;c[f>>2]=Qb[c[(c[(c[e>>2]|0)+8>>2]|0)+24>>2]&15](c[(c[e>>2]|0)+72>>2]|0,0)|0;if((c[f>>2]|0)==0){Ca(5368,4976,1310,5408)}if((c[(c[e>>2]|0)+32>>2]|0)!=0){a=Nh(c[f>>2]|0)|0;c[g>>2]=_f(a+(Nh(c[(c[e>>2]|0)+32>>2]|0)|0)+2|0)|0;a=c[g>>2]|0;h=c[(c[e>>2]|0)+32>>2]|0;c[d>>2]=c[f>>2];c[d+4>>2]=h;cb(a|0,5448,d|0)|0;$f(c[f>>2]|0);i=b;return c[g>>2]|0}else{Ca(5432,4976,1311,5408)}return 0}function Fg(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0;b=i;i=i+32|0;d=b;e=b+20|0;f=b+16|0;g=b+12|0;h=b+8|0;c[f>>2]=a;if((c[(c[f>>2]|0)+40>>2]|0)==0){c[e>>2]=0;j=c[e>>2]|0;i=b;return j|0}c[g>>2]=Qb[c[(c[(c[f>>2]|0)+8>>2]|0)+24>>2]&15](c[(c[f>>2]|0)+72>>2]|0,1)|0;if((c[g>>2]|0)==0){Ca(5368,4976,1326,5456)}a=Nh(c[g>>2]|0)|0;c[h>>2]=_f(a+(Nh(c[(c[f>>2]|0)+40>>2]|0)|0)+2|0)|0;a=c[h>>2]|0;k=c[(c[f>>2]|0)+40>>2]|0;c[d>>2]=c[g>>2];c[d+4>>2]=k;cb(a|0,5480,d|0)|0;$f(c[g>>2]|0);c[e>>2]=c[h>>2];j=c[e>>2]|0;i=b;return j|0}function Gg(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0;e=i;i=i+32|0;f=e+20|0;g=e+16|0;h=e+12|0;j=e+8|0;k=e+4|0;l=e;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;d=c[h>>2]|0;do{if((d|0)==2|(d|0)==1){c[k>>2]=Dg(c[g>>2]|0,c[(c[j>>2]|0)+8>>2]|0,(c[h>>2]|0)==1?1:2)|0;if((c[k>>2]|0)!=0){c[f>>2]=c[k>>2];m=c[f>>2]|0;i=e;return m|0}}else if((d|0)==0){c[l>>2]=Lb[c[(c[(c[g>>2]|0)+8>>2]|0)+44>>2]&15](c[j>>2]|0)|0;c[k>>2]=Qb[c[(c[(c[g>>2]|0)+8>>2]|0)+48>>2]&15](c[l>>2]|0,1)|0;b=c[(c[(c[g>>2]|0)+8>>2]|0)+28>>2]|0;if((c[k>>2]|0)==0){Gb[b&7](c[(c[g>>2]|0)+68>>2]|0);c[(c[g>>2]|0)+68>>2]=c[l>>2];break}Gb[b&7](c[l>>2]|0);c[f>>2]=c[k>>2];m=c[f>>2]|0;i=e;return m|0}}while(0);c[f>>2]=0;m=c[f>>2]|0;i=e;return m|0}function Hg(a){a=a|0;var b=0,d=0,e=0,f=0,h=0,j=0,k=0,l=0.0;b=i;i=i+32|0;d=b+16|0;e=b+12|0;f=b+8|0;h=b+4|0;j=b;c[e>>2]=a;if((c[(c[(c[e>>2]|0)+8>>2]|0)+72>>2]|0)==0){c[d>>2]=5488;k=c[d>>2]|0;i=b;return k|0}if((c[(c[e>>2]|0)+60>>2]|0)<1){c[d>>2]=5536;k=c[d>>2]|0;i=b;return k|0}c[h>>2]=0;c[j>>2]=Db[c[(c[(c[e>>2]|0)+8>>2]|0)+76>>2]&3](c[c[(c[e>>2]|0)+64>>2]>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[e>>2]|0)+44>>2]|0,h)|0;if((c[j>>2]|0)==0){if((c[h>>2]|0)==0){c[h>>2]=5560}c[d>>2]=c[h>>2];k=c[d>>2]|0;i=b;return k|0}c[f>>2]=Qb[c[(c[(c[e>>2]|0)+8>>2]|0)+116>>2]&15](c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[j>>2]|0)|0;if((c[f>>2]|0)==0){Ca(5024,4976,1402,5584)}lg(c[e>>2]|0);rg(c[e>>2]|0);if((c[(c[e>>2]|0)+52>>2]|0)>=(c[(c[e>>2]|0)+56>>2]|0)){c[(c[e>>2]|0)+56>>2]=(c[(c[e>>2]|0)+52>>2]|0)+128;h=ag(c[(c[e>>2]|0)+64>>2]|0,(c[(c[e>>2]|0)+56>>2]|0)*12|0)|0;c[(c[e>>2]|0)+64>>2]=h}c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+52>>2]|0)*12|0)>>2]=c[f>>2];c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+52>>2]|0)*12|0)+4>>2]=c[j>>2];c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+52>>2]|0)*12|0)+8>>2]=2;j=(c[e>>2]|0)+52|0;f=(c[j>>2]|0)+1|0;c[j>>2]=f;c[(c[e>>2]|0)+60>>2]=f;if((c[(c[e>>2]|0)+80>>2]|0)!=0){Nb[c[(c[(c[e>>2]|0)+8>>2]|0)+108>>2]&3](c[(c[e>>2]|0)+80>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-2|0)*12|0)>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0)}c[(c[e>>2]|0)+104>>2]=1;f=c[e>>2]|0;if((c[(c[(c[e>>2]|0)+8>>2]|0)+188>>2]&512|0)!=0){j=Lb[c[(c[f+8>>2]|0)+64>>2]&15](c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-2|0)*12|0)>>2]|0)|0;c[(c[e>>2]|0)+84>>2]=j;l=+Rb[c[(c[(c[e>>2]|0)+8>>2]|0)+148>>2]&3](c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-2|0)*12|0)>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,1,c[(c[e>>2]|0)+80>>2]|0);g[(c[e>>2]|0)+88>>2]=l;g[(c[e>>2]|0)+92>>2]=0.0}else{g[f+88>>2]=0.0;pg(c[e>>2]|0)}if((c[(c[e>>2]|0)+120>>2]|0)!=0){jg(c[e>>2]|0)}mg(c[e>>2]|0);c[d>>2]=0;k=c[d>>2]|0;i=b;return k|0}function Ig(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;d=i;i=i+144|0;e=d;f=d+28|0;h=d+24|0;j=d+20|0;k=d+32|0;l=d+16|0;m=d+12|0;n=d+8|0;c[h>>2]=a;c[j>>2]=b;if((c[(c[h>>2]|0)+116>>2]|0)!=(c[j>>2]|0)){$f(c[(c[h>>2]|0)+116>>2]|0);b=bg(c[j>>2]|0)|0;c[(c[h>>2]|0)+116>>2]=b}if((c[(c[(c[h>>2]|0)+8>>2]|0)+180>>2]|0)!=0){c[n>>2]=~~+g[(c[h>>2]|0)+112>>2];c[m>>2]=(c[n>>2]|0)/60|0;c[n>>2]=(c[n>>2]|0)%60|0;h=c[n>>2]|0;c[e>>2]=c[m>>2];c[e+4>>2]=h;cb(k|0,5600,e|0)|0;e=Nh(k|0)|0;c[l>>2]=_f(e+(Nh(c[j>>2]|0)|0)+1|0)|0;Rh(c[l>>2]|0,k|0)|0;Ph(c[l>>2]|0,c[j>>2]|0)|0;c[f>>2]=c[l>>2];o=c[f>>2]|0;i=d;return o|0}else{c[f>>2]=bg(c[j>>2]|0)|0;o=c[f>>2]|0;i=d;return o|0}return 0}function Jg(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+4|0;e=b;c[e>>2]=a;if((c[(c[e>>2]|0)+60>>2]|0)<=1){c[d>>2]=0;f=c[d>>2]|0;i=b;return f|0}if((c[(c[e>>2]|0)+80>>2]|0)!=0){Nb[c[(c[(c[e>>2]|0)+8>>2]|0)+108>>2]&3](c[(c[e>>2]|0)+80>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-2|0)*12|0)>>2]|0)}a=(c[e>>2]|0)+60|0;c[a>>2]=(c[a>>2]|0)+ -1;c[(c[e>>2]|0)+104>>2]=-1;c[d>>2]=1;f=c[d>>2]|0;i=b;return f|0}function Kg(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+4|0;e=b;c[e>>2]=a;if((c[(c[e>>2]|0)+60>>2]|0)>=(c[(c[e>>2]|0)+52>>2]|0)){c[d>>2]=0;f=c[d>>2]|0;i=b;return f|0}if((c[(c[e>>2]|0)+80>>2]|0)!=0){Nb[c[(c[(c[e>>2]|0)+8>>2]|0)+108>>2]&3](c[(c[e>>2]|0)+80>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+60>>2]|0)*12|0)>>2]|0)}a=(c[e>>2]|0)+60|0;c[a>>2]=(c[a>>2]|0)+1;c[(c[e>>2]|0)+104>>2]=1;c[d>>2]=1;f=c[d>>2]|0;i=b;return f|0}function Lg(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;c[e>>2]=c[d>>2];while(1){if((c[(c[e>>2]|0)+4>>2]|0)==3){break}if((c[(c[e>>2]|0)+4>>2]|0)==0){$f(c[(c[e>>2]|0)+8>>2]|0)}c[e>>2]=(c[e>>2]|0)+16}$f(c[d>>2]|0);i=b;return}function Mg(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;f=i;i=i+32|0;g=f+24|0;h=f+20|0;j=f+16|0;k=f+12|0;l=f+8|0;m=f+4|0;n=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=c[g>>2];c[m>>2]=c[h>>2];while(1){h=c[m>>2]|0;c[m>>2]=h+ -1;if((h|0)<=1){break}c[n>>2]=jh(c[k>>2]|0,(c[m>>2]|0)+1|0)|0;if((c[n>>2]|0)==(c[m>>2]|0)){continue}h=(c[l>>2]|0)+(Z(c[j>>2]|0,c[m>>2]|0)|0)|0;g=(c[l>>2]|0)+(Z(c[j>>2]|0,c[n>>2]|0)|0)|0;Ng(h,g,c[j>>2]|0)}i=f;return}function Ng(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0;e=i;i=i+544|0;f=e+20|0;g=e+16|0;h=e+12|0;j=e+24|0;k=e+8|0;l=e+4|0;m=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;c[k>>2]=c[f>>2];c[l>>2]=c[g>>2];while(1){if((c[h>>2]|0)<=0){break}c[m>>2]=(c[h>>2]|0)>>>0<512?c[h>>2]|0:512;Qh(j|0,c[k>>2]|0,c[m>>2]|0)|0;Qh(c[k>>2]|0,c[l>>2]|0,c[m>>2]|0)|0;Qh(c[l>>2]|0,j|0,c[m>>2]|0)|0;c[k>>2]=(c[k>>2]|0)+(c[m>>2]|0);c[l>>2]=(c[l>>2]|0)+(c[m>>2]|0);c[h>>2]=(c[h>>2]|0)-(c[m>>2]|0)}i=e;return}function Og(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;i=d;return+(+((c[(c[e>>2]|0)+(c[f>>2]<<4)>>2]|0)+(c[(c[e>>2]|0)+(c[f>>2]<<4)+12>>2]|0)|0)*.5877852+ +((c[(c[e>>2]|0)+(c[f>>2]<<4)+4>>2]|0)+(c[(c[e>>2]|0)+(c[f>>2]<<4)+8>>2]|0)|0)*.9510565)}function Pg(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;i=d;return+(+((c[(c[e>>2]|0)+(c[f>>2]<<4)>>2]|0)-(c[(c[e>>2]|0)+(c[f>>2]<<4)+12>>2]|0)|0)*.8090169+ +((c[(c[e>>2]|0)+(c[f>>2]<<4)+4>>2]|0)-(c[(c[e>>2]|0)+(c[f>>2]<<4)+8>>2]|0)|0)*.3090169)}function Qg(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;e=i;i=i+144|0;f=e+128|0;g=e+112|0;h=e+108|0;j=e+104|0;k=e+100|0;l=e+96|0;m=e+80|0;n=e+64|0;o=e+48|0;p=e+32|0;q=e+16|0;r=e;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;Rg(m);Rg(n);d=0-(c[c[j>>2]>>2]|0)|0;c[m+8>>2]=d;c[m+4>>2]=d;c[f+0>>2]=c[m+0>>2];c[f+4>>2]=c[m+4>>2];c[f+8>>2]=c[m+8>>2];c[f+12>>2]=c[m+12>>2];Sg(o,f);c[f+0>>2]=c[o+0>>2];c[f+4>>2]=c[o+4>>2];c[f+8>>2]=c[o+8>>2];c[f+12>>2]=c[o+12>>2];Sg(p,f);c[m+0>>2]=c[p+0>>2];c[m+4>>2]=c[p+4>>2];c[m+8>>2]=c[p+8>>2];c[m+12>>2]=c[p+12>>2];c[n+4>>2]=c[c[j>>2]>>2];p=c[l>>2]|0;c[f+0>>2]=c[m+0>>2];c[f+4>>2]=c[m+4>>2];c[f+8>>2]=c[m+8>>2];c[f+12>>2]=c[m+12>>2];Tg(q,f,p);c[m+0>>2]=c[q+0>>2];c[m+4>>2]=c[q+4>>2];c[m+8>>2]=c[q+8>>2];c[m+12>>2]=c[q+12>>2];q=c[l>>2]|0;c[f+0>>2]=c[n+0>>2];c[f+4>>2]=c[n+4>>2];c[f+8>>2]=c[n+8>>2];c[f+12>>2]=c[n+12>>2];Tg(r,f,q);c[n+0>>2]=c[r+0>>2];c[n+4>>2]=c[r+4>>2];c[n+8>>2]=c[r+8>>2];c[n+12>>2]=c[r+12>>2];r=c[j>>2]|0;if((c[k>>2]|0)==0){c[g+0>>2]=c[m+0>>2];c[g+4>>2]=c[m+4>>2];c[g+8>>2]=c[m+8>>2];c[g+12>>2]=c[m+12>>2];c[f+0>>2]=c[n+0>>2];c[f+4>>2]=c[n+4>>2];c[f+8>>2]=c[n+8>>2];c[f+12>>2]=c[n+12>>2];c[h>>2]=Ug(r,0,1,g,f)|0;s=c[h>>2]|0;i=e;return s|0}else{c[g+0>>2]=c[m+0>>2];c[g+4>>2]=c[m+4>>2];c[g+8>>2]=c[m+8>>2];c[g+12>>2]=c[m+12>>2];c[f+0>>2]=c[n+0>>2];c[f+4>>2]=c[n+4>>2];c[f+8>>2]=c[n+8>>2];c[f+12>>2]=c[n+12>>2];c[h>>2]=Vg(r,0,1,g,f)|0;s=c[h>>2]|0;i=e;return s|0}return 0}function Rg(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d+12>>2]=0;c[d+8>>2]=0;c[d+4>>2]=0;c[d>>2]=0;c[a+0>>2]=c[d+0>>2];c[a+4>>2]=c[d+4>>2];c[a+8>>2]=c[d+8>>2];c[a+12>>2]=c[d+12>>2];i=b;return}function Sg(a,b){a=a|0;b=b|0;var d=0,e=0;d=i;i=i+16|0;e=d;c[e>>2]=(c[b+4>>2]|0)-(c[b+12>>2]|0);c[e+4>>2]=(c[b+8>>2]|0)+(c[b+12>>2]|0)-(c[b+4>>2]|0);c[e+8>>2]=(c[b>>2]|0)+(c[b+4>>2]|0)-(c[b+8>>2]|0);c[e+12>>2]=(c[b+8>>2]|0)-(c[b>>2]|0);c[a+0>>2]=c[e+0>>2];c[a+4>>2]=c[e+4>>2];c[a+8>>2]=c[e+8>>2];c[a+12>>2]=c[e+12>>2];i=d;return}function Tg(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0;e=i;i=i+48|0;f=e+24|0;g=e+20|0;h=e+16|0;j=e;c[g>>2]=d;if(((c[g>>2]|0)%36|0|0)!=0){Ca(5680,5696,164,5712)}while(1){k=c[g>>2]|0;if((c[g>>2]|0)>=0){break}c[g>>2]=k+360}c[g>>2]=360-k;c[h>>2]=0;while(1){if((c[h>>2]|0)>=((c[g>>2]|0)/36|0|0)){break}c[f+0>>2]=c[b+0>>2];c[f+4>>2]=c[b+4>>2];c[f+8>>2]=c[b+8>>2];c[f+12>>2]=c[b+12>>2];ah(j,f);c[b+0>>2]=c[j+0>>2];c[b+4>>2]=c[j+4>>2];c[b+8>>2]=c[j+8>>2];c[b+12>>2]=c[j+12>>2];c[h>>2]=(c[h>>2]|0)+1}c[a+0>>2]=c[b+0>>2];c[a+4>>2]=c[b+4>>2];c[a+8>>2]=c[b+8>>2];c[a+12>>2]=c[b+12>>2];i=e;return}function Ug(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0;g=i;i=i+288|0;h=g+272|0;j=g+256|0;k=g+252|0;l=g+248|0;m=g+244|0;n=g+240|0;o=g+224|0;p=g+208|0;q=g+144|0;r=g+128|0;s=g+112|0;t=g+96|0;u=g+80|0;v=g+64|0;w=g+48|0;x=g+32|0;y=g+16|0;z=g;c[l>>2]=a;c[m>>2]=b;c[n>>2]=d;if((c[n>>2]|0)>0){c[q+0>>2]=c[e+0>>2];c[q+4>>2]=c[e+4>>2];c[q+8>>2]=c[e+8>>2];c[q+12>>2]=c[e+12>>2];d=q+16|0;c[j+0>>2]=c[f+0>>2];c[j+4>>2]=c[f+4>>2];c[j+8>>2]=c[f+8>>2];c[j+12>>2]=c[f+12>>2];c[h+0>>2]=c[q+0>>2];c[h+4>>2]=c[q+4>>2];c[h+8>>2]=c[q+8>>2];c[h+12>>2]=c[q+12>>2];Xg(r,j,0,h,-36);c[d+0>>2]=c[r+0>>2];c[d+4>>2]=c[r+4>>2];c[d+8>>2]=c[r+8>>2];c[d+12>>2]=c[r+12>>2];r=q+32|0;c[j+0>>2]=c[f+0>>2];c[j+4>>2]=c[f+4>>2];c[j+8>>2]=c[f+8>>2];c[j+12>>2]=c[f+12>>2];c[h+0>>2]=c[q+0>>2];c[h+4>>2]=c[q+4>>2];c[h+8>>2]=c[q+8>>2];c[h+12>>2]=c[q+12>>2];Xg(s,j,0,h,0);c[r+0>>2]=c[s+0>>2];c[r+4>>2]=c[s+4>>2];c[r+8>>2]=c[s+8>>2];c[r+12>>2]=c[s+12>>2];s=q+48|0;c[j+0>>2]=c[f+0>>2];c[j+4>>2]=c[f+4>>2];c[j+8>>2]=c[f+8>>2];c[j+12>>2]=c[f+12>>2];c[h+0>>2]=c[q+0>>2];c[h+4>>2]=c[q+4>>2];c[h+8>>2]=c[q+8>>2];c[h+12>>2]=c[q+12>>2];Xg(t,j,0,h,36);c[s+0>>2]=c[t+0>>2];c[s+4>>2]=c[t+4>>2];c[s+8>>2]=c[t+8>>2];c[s+12>>2]=c[t+12>>2];Db[c[(c[l>>2]|0)+8>>2]&3](c[l>>2]|0,q,4,c[m>>2]|0)|0}if((c[m>>2]|0)>=(c[(c[l>>2]|0)+4>>2]|0)){c[k>>2]=0;A=c[k>>2]|0;i=g;return A|0}else{q=Z(-36,c[n>>2]|0)|0;c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];Tg(u,h,q);c[j+0>>2]=c[e+0>>2];c[j+4>>2]=c[e+4>>2];c[j+8>>2]=c[e+8>>2];c[j+12>>2]=c[e+12>>2];c[h+0>>2]=c[u+0>>2];c[h+4>>2]=c[u+4>>2];c[h+8>>2]=c[u+8>>2];c[h+12>>2]=c[u+12>>2];Yg(v,j,h);c[o+0>>2]=c[v+0>>2];c[o+4>>2]=c[v+4>>2];c[o+8>>2]=c[v+8>>2];c[o+12>>2]=c[v+12>>2];v=(c[n>>2]|0)*108|0;c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];Tg(w,h,v);c[p+0>>2]=c[w+0>>2];c[p+4>>2]=c[w+4>>2];c[p+8>>2]=c[w+8>>2];c[p+12>>2]=c[w+12>>2];w=c[l>>2]|0;v=(c[m>>2]|0)+1|0;u=c[n>>2]|0;c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];Sg(x,h);c[j+0>>2]=c[e+0>>2];c[j+4>>2]=c[e+4>>2];c[j+8>>2]=c[e+8>>2];c[j+12>>2]=c[e+12>>2];c[h+0>>2]=c[x+0>>2];c[h+4>>2]=c[x+4>>2];c[h+8>>2]=c[x+8>>2];c[h+12>>2]=c[x+12>>2];$g(w,v,u,j,h)|0;u=c[l>>2]|0;v=(c[m>>2]|0)+1|0;w=c[n>>2]|0;c[h+0>>2]=c[p+0>>2];c[h+4>>2]=c[p+4>>2];c[h+8>>2]=c[p+8>>2];c[h+12>>2]=c[p+12>>2];Sg(y,h);c[j+0>>2]=c[o+0>>2];c[j+4>>2]=c[o+4>>2];c[j+8>>2]=c[o+8>>2];c[j+12>>2]=c[o+12>>2];c[h+0>>2]=c[y+0>>2];c[h+4>>2]=c[y+4>>2];c[h+8>>2]=c[y+8>>2];c[h+12>>2]=c[y+12>>2];Ug(u,v,w,j,h)|0;w=c[l>>2]|0;l=(c[m>>2]|0)+1|0;m=0-(c[n>>2]|0)|0;c[h+0>>2]=c[p+0>>2];c[h+4>>2]=c[p+4>>2];c[h+8>>2]=c[p+8>>2];c[h+12>>2]=c[p+12>>2];Sg(z,h);c[j+0>>2]=c[o+0>>2];c[j+4>>2]=c[o+4>>2];c[j+8>>2]=c[o+8>>2];c[j+12>>2]=c[o+12>>2];c[h+0>>2]=c[z+0>>2];c[h+4>>2]=c[z+4>>2];c[h+8>>2]=c[z+8>>2];c[h+12>>2]=c[z+12>>2];Ug(w,l,m,j,h)|0;c[k>>2]=0;A=c[k>>2]|0;i=g;return A|0}return 0}function Vg(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;g=i;i=i+256|0;h=g+240|0;j=g+224|0;k=g+220|0;l=g+216|0;m=g+212|0;n=g+208|0;o=g+192|0;p=g+128|0;q=g+112|0;r=g+96|0;s=g+80|0;t=g+64|0;u=g+48|0;v=g+32|0;w=g+16|0;x=g;c[l>>2]=a;c[m>>2]=b;c[n>>2]=d;if((c[n>>2]|0)>0){c[p+0>>2]=c[e+0>>2];c[p+4>>2]=c[e+4>>2];c[p+8>>2]=c[e+8>>2];c[p+12>>2]=c[e+12>>2];d=p+16|0;c[j+0>>2]=c[f+0>>2];c[j+4>>2]=c[f+4>>2];c[j+8>>2]=c[f+8>>2];c[j+12>>2]=c[f+12>>2];c[h+0>>2]=c[p+0>>2];c[h+4>>2]=c[p+4>>2];c[h+8>>2]=c[p+8>>2];c[h+12>>2]=c[p+12>>2];Xg(q,j,0,h,-36);c[d+0>>2]=c[q+0>>2];c[d+4>>2]=c[q+4>>2];c[d+8>>2]=c[q+8>>2];c[d+12>>2]=c[q+12>>2];q=p+48|0;c[j+0>>2]=c[f+0>>2];c[j+4>>2]=c[f+4>>2];c[j+8>>2]=c[f+8>>2];c[j+12>>2]=c[f+12>>2];c[h+0>>2]=c[p+0>>2];c[h+4>>2]=c[p+4>>2];c[h+8>>2]=c[p+8>>2];c[h+12>>2]=c[p+12>>2];Xg(r,j,0,h,0);c[q+0>>2]=c[r+0>>2];c[q+4>>2]=c[r+4>>2];c[q+8>>2]=c[r+8>>2];c[q+12>>2]=c[r+12>>2];r=p+32|0;q=p+48|0;c[j+0>>2]=c[f+0>>2];c[j+4>>2]=c[f+4>>2];c[j+8>>2]=c[f+8>>2];c[j+12>>2]=c[f+12>>2];c[h+0>>2]=c[q+0>>2];c[h+4>>2]=c[q+4>>2];c[h+8>>2]=c[q+8>>2];c[h+12>>2]=c[q+12>>2];Xg(s,j,0,h,-36);c[r+0>>2]=c[s+0>>2];c[r+4>>2]=c[s+4>>2];c[r+8>>2]=c[s+8>>2];c[r+12>>2]=c[s+12>>2];Db[c[(c[l>>2]|0)+8>>2]&3](c[l>>2]|0,p,4,c[m>>2]|0)|0}if((c[m>>2]|0)>=(c[(c[l>>2]|0)+4>>2]|0)){c[k>>2]=0;y=c[k>>2]|0;i=g;return y|0}else{c[j+0>>2]=c[e+0>>2];c[j+4>>2]=c[e+4>>2];c[j+8>>2]=c[e+8>>2];c[j+12>>2]=c[e+12>>2];c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];Yg(t,j,h);c[o+0>>2]=c[t+0>>2];c[o+4>>2]=c[t+4>>2];c[o+8>>2]=c[t+8>>2];c[o+12>>2]=c[t+12>>2];t=c[l>>2]|0;e=(c[m>>2]|0)+1|0;p=0-(c[n>>2]|0)|0;c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];Tg(v,h,180);c[h+0>>2]=c[v+0>>2];c[h+4>>2]=c[v+4>>2];c[h+8>>2]=c[v+8>>2];c[h+12>>2]=c[v+12>>2];Sg(u,h);c[j+0>>2]=c[o+0>>2];c[j+4>>2]=c[o+4>>2];c[j+8>>2]=c[o+8>>2];c[j+12>>2]=c[o+12>>2];c[h+0>>2]=c[u+0>>2];c[h+4>>2]=c[u+4>>2];c[h+8>>2]=c[u+8>>2];c[h+12>>2]=c[u+12>>2];Zg(t,e,p,j,h)|0;p=c[l>>2]|0;l=(c[m>>2]|0)+1|0;m=c[n>>2]|0;e=Z(-108,c[n>>2]|0)|0;c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];Tg(x,h,e);c[h+0>>2]=c[x+0>>2];c[h+4>>2]=c[x+4>>2];c[h+8>>2]=c[x+8>>2];c[h+12>>2]=c[x+12>>2];Sg(w,h);c[j+0>>2]=c[o+0>>2];c[j+4>>2]=c[o+4>>2];c[j+8>>2]=c[o+8>>2];c[j+12>>2]=c[o+12>>2];c[h+0>>2]=c[w+0>>2];c[h+4>>2]=c[w+4>>2];c[h+8>>2]=c[w+8>>2];c[h+12>>2]=c[w+12>>2];Vg(p,l,m,j,h)|0;c[k>>2]=0;y=c[k>>2]|0;i=g;return y|0}return 0}function Wg(a,b,d,e,f,g,j){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0;k=i;i=i+48|0;l=k+44|0;m=k+40|0;n=k+36|0;o=k+32|0;p=k+28|0;q=k+24|0;r=k+20|0;s=k+8|0;t=k;u=k+16|0;c[l>>2]=a;c[m>>2]=b;c[n>>2]=d;c[o>>2]=e;c[p>>2]=f;c[q>>2]=g;c[r>>2]=j;c[u>>2]=0;j=c[m>>2]|0;if((c[l>>2]|0)==0){c[m>>2]=(j*3|0)/2|0}else{c[m>>2]=(j*5|0)/4|0}j=Z(c[n>>2]|0,c[n>>2]|0)|0;h[s>>3]=+(c[m>>2]|0)*3.11*+N(+(+(j+(Z(c[o>>2]|0,c[o>>2]|0)|0)|0)));h[t>>3]=+(c[m>>2]|0);while(1){if(!(+h[t>>3]*.22426<+h[s>>3])){break}c[u>>2]=(c[u>>2]|0)+1;h[t>>3]=+h[t>>3]*1.6180339887}c[c[q>>2]>>2]=~~+h[t>>3];c[c[r>>2]>>2]=c[u>>2];h[c[p>>2]>>3]=+h[s>>3];i=k;return}function Xg(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0;g=i;i=i+112|0;h=g+88|0;j=g+72|0;k=g+68|0;l=g+64|0;m=g+48|0;n=g+32|0;o=g+16|0;p=g;c[k>>2]=d;c[l>>2]=f;if((c[k>>2]|0)>=0){if((c[k>>2]|0)>0){c[h+0>>2]=c[b+0>>2];c[h+4>>2]=c[b+4>>2];c[h+8>>2]=c[b+8>>2];c[h+12>>2]=c[b+12>>2];_g(n,h);c[b+0>>2]=c[n+0>>2];c[b+4>>2]=c[n+4>>2];c[b+8>>2]=c[n+8>>2];c[b+12>>2]=c[n+12>>2]}}else{c[h+0>>2]=c[b+0>>2];c[h+4>>2]=c[b+4>>2];c[h+8>>2]=c[b+8>>2];c[h+12>>2]=c[b+12>>2];Sg(m,h);c[b+0>>2]=c[m+0>>2];c[b+4>>2]=c[m+4>>2];c[b+8>>2]=c[m+8>>2];c[b+12>>2]=c[m+12>>2]}m=c[l>>2]|0;c[h+0>>2]=c[b+0>>2];c[h+4>>2]=c[b+4>>2];c[h+8>>2]=c[b+8>>2];c[h+12>>2]=c[b+12>>2];Tg(o,h,m);c[b+0>>2]=c[o+0>>2];c[b+4>>2]=c[o+4>>2];c[b+8>>2]=c[o+8>>2];c[b+12>>2]=c[o+12>>2];c[j+0>>2]=c[b+0>>2];c[j+4>>2]=c[b+4>>2];c[j+8>>2]=c[b+8>>2];c[j+12>>2]=c[b+12>>2];c[h+0>>2]=c[e+0>>2];c[h+4>>2]=c[e+4>>2];c[h+8>>2]=c[e+8>>2];c[h+12>>2]=c[e+12>>2];Yg(p,j,h);c[b+0>>2]=c[p+0>>2];c[b+4>>2]=c[p+4>>2];c[b+8>>2]=c[p+8>>2];c[b+12>>2]=c[p+12>>2];c[a+0>>2]=c[b+0>>2];c[a+4>>2]=c[b+4>>2];c[a+8>>2]=c[b+8>>2];c[a+12>>2]=c[b+12>>2];i=g;return}function Yg(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0;e=i;c[b>>2]=(c[b>>2]|0)+(c[d>>2]|0);f=b+4|0;c[f>>2]=(c[f>>2]|0)+(c[d+4>>2]|0);f=b+8|0;c[f>>2]=(c[f>>2]|0)+(c[d+8>>2]|0);f=b+12|0;c[f>>2]=(c[f>>2]|0)+(c[d+12>>2]|0);c[a+0>>2]=c[b+0>>2];c[a+4>>2]=c[b+4>>2];c[a+8>>2]=c[b+8>>2];c[a+12>>2]=c[b+12>>2];i=e;return}function Zg(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0;g=i;i=i+320|0;h=g+304|0;j=g+288|0;k=g+284|0;l=g+280|0;m=g+276|0;n=g+272|0;o=g+256|0;p=g+192|0;q=g+176|0;r=g+160|0;s=g+144|0;t=g+128|0;u=g+112|0;v=g+96|0;w=g+80|0;x=g+64|0;y=g+48|0;z=g+32|0;A=g+16|0;B=g;c[l>>2]=a;c[m>>2]=b;c[n>>2]=d;if((c[n>>2]|0)>0){c[p+0>>2]=c[e+0>>2];c[p+4>>2]=c[e+4>>2];c[p+8>>2]=c[e+8>>2];c[p+12>>2]=c[e+12>>2];d=p+16|0;c[j+0>>2]=c[f+0>>2];c[j+4>>2]=c[f+4>>2];c[j+8>>2]=c[f+8>>2];c[j+12>>2]=c[f+12>>2];c[h+0>>2]=c[p+0>>2];c[h+4>>2]=c[p+4>>2];c[h+8>>2]=c[p+8>>2];c[h+12>>2]=c[p+12>>2];Xg(q,j,0,h,-36);c[d+0>>2]=c[q+0>>2];c[d+4>>2]=c[q+4>>2];c[d+8>>2]=c[q+8>>2];c[d+12>>2]=c[q+12>>2];q=p+32|0;c[j+0>>2]=c[f+0>>2];c[j+4>>2]=c[f+4>>2];c[j+8>>2]=c[f+8>>2];c[j+12>>2]=c[f+12>>2];c[h+0>>2]=c[p+0>>2];c[h+4>>2]=c[p+4>>2];c[h+8>>2]=c[p+8>>2];c[h+12>>2]=c[p+12>>2];Xg(r,j,1,h,0);c[q+0>>2]=c[r+0>>2];c[q+4>>2]=c[r+4>>2];c[q+8>>2]=c[r+8>>2];c[q+12>>2]=c[r+12>>2];r=p+48|0;c[j+0>>2]=c[f+0>>2];c[j+4>>2]=c[f+4>>2];c[j+8>>2]=c[f+8>>2];c[j+12>>2]=c[f+12>>2];c[h+0>>2]=c[p+0>>2];c[h+4>>2]=c[p+4>>2];c[h+8>>2]=c[p+8>>2];c[h+12>>2]=c[p+12>>2];Xg(s,j,0,h,36);c[r+0>>2]=c[s+0>>2];c[r+4>>2]=c[s+4>>2];c[r+8>>2]=c[s+8>>2];c[r+12>>2]=c[s+12>>2];Db[c[(c[l>>2]|0)+8>>2]&3](c[l>>2]|0,p,4,c[m>>2]|0)|0}if((c[m>>2]|0)>=(c[(c[l>>2]|0)+4>>2]|0)){c[k>>2]=0;C=c[k>>2]|0;i=g;return C|0}else{c[j+0>>2]=c[e+0>>2];c[j+4>>2]=c[e+4>>2];c[j+8>>2]=c[e+8>>2];c[j+12>>2]=c[e+12>>2];c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];Yg(t,j,h);c[o+0>>2]=c[t+0>>2];c[o+4>>2]=c[t+4>>2];c[o+8>>2]=c[t+8>>2];c[o+12>>2]=c[t+12>>2];t=c[l>>2]|0;p=(c[m>>2]|0)+1|0;s=0-(c[n>>2]|0)|0;c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];Tg(v,h,180);c[h+0>>2]=c[v+0>>2];c[h+4>>2]=c[v+4>>2];c[h+8>>2]=c[v+8>>2];c[h+12>>2]=c[v+12>>2];Sg(u,h);c[j+0>>2]=c[o+0>>2];c[j+4>>2]=c[o+4>>2];c[j+8>>2]=c[o+8>>2];c[j+12>>2]=c[o+12>>2];c[h+0>>2]=c[u+0>>2];c[h+4>>2]=c[u+4>>2];c[h+8>>2]=c[u+8>>2];c[h+12>>2]=c[u+12>>2];Zg(t,p,s,j,h)|0;s=c[l>>2]|0;p=(c[m>>2]|0)+1|0;t=c[n>>2]|0;u=Z(-108,c[n>>2]|0)|0;c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];Tg(x,h,u);c[h+0>>2]=c[x+0>>2];c[h+4>>2]=c[x+4>>2];c[h+8>>2]=c[x+8>>2];c[h+12>>2]=c[x+12>>2];Sg(w,h);c[j+0>>2]=c[o+0>>2];c[j+4>>2]=c[o+4>>2];c[j+8>>2]=c[o+8>>2];c[j+12>>2]=c[o+12>>2];c[h+0>>2]=c[w+0>>2];c[h+4>>2]=c[w+4>>2];c[h+8>>2]=c[w+8>>2];c[h+12>>2]=c[w+12>>2];Vg(s,p,t,j,h)|0;c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];_g(y,h);c[j+0>>2]=c[e+0>>2];c[j+4>>2]=c[e+4>>2];c[j+8>>2]=c[e+8>>2];c[j+12>>2]=c[e+12>>2];c[h+0>>2]=c[y+0>>2];c[h+4>>2]=c[y+4>>2];c[h+8>>2]=c[y+8>>2];c[h+12>>2]=c[y+12>>2];Yg(z,j,h);c[o+0>>2]=c[z+0>>2];c[o+4>>2]=c[z+4>>2];c[o+8>>2]=c[z+8>>2];c[o+12>>2]=c[z+12>>2];z=c[l>>2]|0;l=(c[m>>2]|0)+1|0;m=c[n>>2]|0;y=Z(-144,c[n>>2]|0)|0;c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];Tg(B,h,y);c[h+0>>2]=c[B+0>>2];c[h+4>>2]=c[B+4>>2];c[h+8>>2]=c[B+8>>2];c[h+12>>2]=c[B+12>>2];Sg(A,h);c[j+0>>2]=c[o+0>>2];c[j+4>>2]=c[o+4>>2];c[j+8>>2]=c[o+8>>2];c[j+12>>2]=c[o+12>>2];c[h+0>>2]=c[A+0>>2];c[h+4>>2]=c[A+4>>2];c[h+8>>2]=c[A+8>>2];c[h+12>>2]=c[A+12>>2];Zg(z,l,m,j,h)|0;c[k>>2]=0;C=c[k>>2]|0;i=g;return C|0}return 0}function _g(a,b){a=a|0;b=b|0;var d=0,e=0;d=i;i=i+16|0;e=d;c[e>>2]=(c[b>>2]|0)+(c[b+4>>2]|0)-(c[b+12>>2]|0);c[e+4>>2]=(c[b+8>>2]|0)+(c[b+12>>2]|0);c[e+8>>2]=(c[b>>2]|0)+(c[b+4>>2]|0);c[e+12>>2]=(c[b+8>>2]|0)+(c[b+12>>2]|0)-(c[b>>2]|0);c[a+0>>2]=c[e+0>>2];c[a+4>>2]=c[e+4>>2];c[a+8>>2]=c[e+8>>2];c[a+12>>2]=c[e+12>>2];i=d;return}function $g(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;g=i;i=i+256|0;h=g+240|0;j=g+224|0;k=g+220|0;l=g+216|0;m=g+212|0;n=g+208|0;o=g+192|0;p=g+128|0;q=g+112|0;r=g+96|0;s=g+80|0;t=g+64|0;u=g+48|0;v=g+32|0;w=g+16|0;x=g;c[l>>2]=a;c[m>>2]=b;c[n>>2]=d;if((c[n>>2]|0)>0){c[p+0>>2]=c[e+0>>2];c[p+4>>2]=c[e+4>>2];c[p+8>>2]=c[e+8>>2];c[p+12>>2]=c[e+12>>2];d=p+16|0;c[j+0>>2]=c[f+0>>2];c[j+4>>2]=c[f+4>>2];c[j+8>>2]=c[f+8>>2];c[j+12>>2]=c[f+12>>2];c[h+0>>2]=c[p+0>>2];c[h+4>>2]=c[p+4>>2];c[h+8>>2]=c[p+8>>2];c[h+12>>2]=c[p+12>>2];Xg(q,j,0,h,-72);c[d+0>>2]=c[q+0>>2];c[d+4>>2]=c[q+4>>2];c[d+8>>2]=c[q+8>>2];c[d+12>>2]=c[q+12>>2];q=p+32|0;c[j+0>>2]=c[f+0>>2];c[j+4>>2]=c[f+4>>2];c[j+8>>2]=c[f+8>>2];c[j+12>>2]=c[f+12>>2];c[h+0>>2]=c[p+0>>2];c[h+4>>2]=c[p+4>>2];c[h+8>>2]=c[p+8>>2];c[h+12>>2]=c[p+12>>2];Xg(r,j,-1,h,-36);c[q+0>>2]=c[r+0>>2];c[q+4>>2]=c[r+4>>2];c[q+8>>2]=c[r+8>>2];c[q+12>>2]=c[r+12>>2];r=p+48|0;c[j+0>>2]=c[f+0>>2];c[j+4>>2]=c[f+4>>2];c[j+8>>2]=c[f+8>>2];c[j+12>>2]=c[f+12>>2];c[h+0>>2]=c[p+0>>2];c[h+4>>2]=c[p+4>>2];c[h+8>>2]=c[p+8>>2];c[h+12>>2]=c[p+12>>2];Xg(s,j,0,h,0);c[r+0>>2]=c[s+0>>2];c[r+4>>2]=c[s+4>>2];c[r+8>>2]=c[s+8>>2];c[r+12>>2]=c[s+12>>2];Db[c[(c[l>>2]|0)+8>>2]&3](c[l>>2]|0,p,4,c[m>>2]|0)|0}if((c[m>>2]|0)>=(c[(c[l>>2]|0)+4>>2]|0)){c[k>>2]=0;y=c[k>>2]|0;i=g;return y|0}else{c[j+0>>2]=c[e+0>>2];c[j+4>>2]=c[e+4>>2];c[j+8>>2]=c[e+8>>2];c[j+12>>2]=c[e+12>>2];c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];Yg(t,j,h);c[o+0>>2]=c[t+0>>2];c[o+4>>2]=c[t+4>>2];c[o+8>>2]=c[t+8>>2];c[o+12>>2]=c[t+12>>2];t=c[l>>2]|0;p=(c[m>>2]|0)+1|0;s=0-(c[n>>2]|0)|0;r=Z(-36,c[n>>2]|0)|0;c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];Tg(v,h,r);c[h+0>>2]=c[v+0>>2];c[h+4>>2]=c[v+4>>2];c[h+8>>2]=c[v+8>>2];c[h+12>>2]=c[v+12>>2];Sg(u,h);c[j+0>>2]=c[e+0>>2];c[j+4>>2]=c[e+4>>2];c[j+8>>2]=c[e+8>>2];c[j+12>>2]=c[e+12>>2];c[h+0>>2]=c[u+0>>2];c[h+4>>2]=c[u+4>>2];c[h+8>>2]=c[u+8>>2];c[h+12>>2]=c[u+12>>2];Ug(t,p,s,j,h)|0;s=c[l>>2]|0;l=(c[m>>2]|0)+1|0;m=c[n>>2]|0;p=Z(-144,c[n>>2]|0)|0;c[h+0>>2]=c[f+0>>2];c[h+4>>2]=c[f+4>>2];c[h+8>>2]=c[f+8>>2];c[h+12>>2]=c[f+12>>2];Tg(x,h,p);c[h+0>>2]=c[x+0>>2];c[h+4>>2]=c[x+4>>2];c[h+8>>2]=c[x+8>>2];c[h+12>>2]=c[x+12>>2];Sg(w,h);c[j+0>>2]=c[o+0>>2];c[j+4>>2]=c[o+4>>2];c[j+8>>2]=c[o+8>>2];c[j+12>>2]=c[o+12>>2];c[h+0>>2]=c[w+0>>2];c[h+4>>2]=c[w+4>>2];c[h+8>>2]=c[w+8>>2];c[h+12>>2]=c[w+12>>2];$g(s,l,m,j,h)|0;c[k>>2]=0;y=c[k>>2]|0;i=g;return y|0}return 0}function ah(a,b){a=a|0;b=b|0;var d=0,e=0;d=i;i=i+16|0;e=d;c[e>>2]=0-(c[b+12>>2]|0);c[e+4>>2]=(c[b+12>>2]|0)+(c[b>>2]|0);c[e+8>>2]=0-(c[b+12>>2]|0)+(c[b+4>>2]|0);c[e+12>>2]=(c[b+12>>2]|0)+(c[b+8>>2]|0);c[a+0>>2]=c[e+0>>2];c[a+4>>2]=c[e+4>>2];c[a+8>>2]=c[e+8>>2];c[a+12>>2]=c[e+12>>2];i=d;return}function bh(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;ch(c[d>>2]|0);c[(c[d>>2]|0)+84>>2]=0;c[(c[d>>2]|0)+92>>2]=0;c[(c[d>>2]|0)+88>>2]=0;i=b;return}function ch(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;c[c[d>>2]>>2]=1732584193;c[(c[d>>2]|0)+4>>2]=-271733879;c[(c[d>>2]|0)+8>>2]=-1732584194;c[(c[d>>2]|0)+12>>2]=271733878;c[(c[d>>2]|0)+16>>2]=-1009589776;i=b;return}function dh(a,b,e){a=a|0;b=b|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;f=i;i=i+96|0;g=f+84|0;h=f+80|0;j=f+76|0;k=f+72|0;l=f+8|0;m=f+4|0;n=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=e;c[k>>2]=c[h>>2];c[m>>2]=c[j>>2];h=(c[g>>2]|0)+92|0;c[h>>2]=(c[h>>2]|0)+(c[m>>2]|0);h=(c[g>>2]|0)+88|0;c[h>>2]=(c[h>>2]|0)+((c[(c[g>>2]|0)+92>>2]|0)>>>0<(c[m>>2]|0)>>>0);if((c[(c[g>>2]|0)+84>>2]|0)!=0?((c[(c[g>>2]|0)+84>>2]|0)+(c[j>>2]|0)|0)<64:0){Qh((c[g>>2]|0)+20+(c[(c[g>>2]|0)+84>>2]|0)|0,c[k>>2]|0,c[j>>2]|0)|0;m=(c[g>>2]|0)+84|0;c[m>>2]=(c[m>>2]|0)+(c[j>>2]|0);i=f;return}while(1){o=(c[g>>2]|0)+20|0;if(((c[(c[g>>2]|0)+84>>2]|0)+(c[j>>2]|0)|0)<64){break}Qh(o+(c[(c[g>>2]|0)+84>>2]|0)|0,c[k>>2]|0,64-(c[(c[g>>2]|0)+84>>2]|0)|0)|0;c[k>>2]=(c[k>>2]|0)+(64-(c[(c[g>>2]|0)+84>>2]|0));c[j>>2]=(c[j>>2]|0)-(64-(c[(c[g>>2]|0)+84>>2]|0));c[n>>2]=0;while(1){if((c[n>>2]|0)>=16){break}c[l+(c[n>>2]<<2)>>2]=(d[(c[g>>2]|0)+20+((c[n>>2]<<2)+0)|0]|0)<<24|(d[(c[g>>2]|0)+20+((c[n>>2]<<2)+1)|0]|0)<<16|(d[(c[g>>2]|0)+20+((c[n>>2]<<2)+2)|0]|0)<<8|(d[(c[g>>2]|0)+20+((c[n>>2]<<2)+3)|0]|0)<<0;c[n>>2]=(c[n>>2]|0)+1}eh(c[g>>2]|0,l);c[(c[g>>2]|0)+84>>2]=0}Qh(o|0,c[k>>2]|0,c[j>>2]|0)|0;c[(c[g>>2]|0)+84>>2]=c[j>>2];i=f;return}function eh(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;d=i;i=i+384|0;e=d+372|0;f=d+368|0;g=d+48|0;h=d+40|0;j=d+36|0;k=d+32|0;l=d+28|0;m=d+24|0;n=d+20|0;o=d+16|0;p=d+12|0;q=d+8|0;r=d+4|0;s=d;c[e>>2]=a;c[f>>2]=b;c[n>>2]=0;while(1){if((c[n>>2]|0)>=16){break}c[g+(c[n>>2]<<2)>>2]=c[(c[f>>2]|0)+(c[n>>2]<<2)>>2];c[n>>2]=(c[n>>2]|0)+1}c[n>>2]=16;while(1){if((c[n>>2]|0)>=80){break}c[o>>2]=c[g+((c[n>>2]|0)-3<<2)>>2]^c[g+((c[n>>2]|0)-8<<2)>>2]^c[g+((c[n>>2]|0)-14<<2)>>2]^c[g+((c[n>>2]|0)-16<<2)>>2];c[g+(c[n>>2]<<2)>>2]=c[o>>2]<<1|(c[o>>2]|0)>>>31;c[n>>2]=(c[n>>2]|0)+1}c[h>>2]=c[c[e>>2]>>2];c[j>>2]=c[(c[e>>2]|0)+4>>2];c[k>>2]=c[(c[e>>2]|0)+8>>2];c[l>>2]=c[(c[e>>2]|0)+12>>2];c[m>>2]=c[(c[e>>2]|0)+16>>2];c[n>>2]=0;while(1){if((c[n>>2]|0)>=20){break}c[p>>2]=(c[h>>2]<<5|(c[h>>2]|0)>>>27)+(c[j>>2]&c[k>>2]|c[l>>2]&~c[j>>2])+(c[m>>2]|0)+(c[g+(c[n>>2]<<2)>>2]|0)+1518500249;c[m>>2]=c[l>>2];c[l>>2]=c[k>>2];c[k>>2]=c[j>>2]<<30|(c[j>>2]|0)>>>2;c[j>>2]=c[h>>2];c[h>>2]=c[p>>2];c[n>>2]=(c[n>>2]|0)+1}c[n>>2]=20;while(1){if((c[n>>2]|0)>=40){break}c[q>>2]=(c[h>>2]<<5|(c[h>>2]|0)>>>27)+(c[j>>2]^c[k>>2]^c[l>>2])+(c[m>>2]|0)+(c[g+(c[n>>2]<<2)>>2]|0)+1859775393;c[m>>2]=c[l>>2];c[l>>2]=c[k>>2];c[k>>2]=c[j>>2]<<30|(c[j>>2]|0)>>>2;c[j>>2]=c[h>>2];c[h>>2]=c[q>>2];c[n>>2]=(c[n>>2]|0)+1}c[n>>2]=40;while(1){if((c[n>>2]|0)>=60){break}c[r>>2]=(c[h>>2]<<5|(c[h>>2]|0)>>>27)+(c[j>>2]&c[k>>2]|c[j>>2]&c[l>>2]|c[k>>2]&c[l>>2])+(c[m>>2]|0)+(c[g+(c[n>>2]<<2)>>2]|0)+ -1894007588;c[m>>2]=c[l>>2];c[l>>2]=c[k>>2];c[k>>2]=c[j>>2]<<30|(c[j>>2]|0)>>>2;c[j>>2]=c[h>>2];c[h>>2]=c[r>>2];c[n>>2]=(c[n>>2]|0)+1}c[n>>2]=60;while(1){t=c[h>>2]|0;if((c[n>>2]|0)>=80){break}c[s>>2]=(t<<5|(c[h>>2]|0)>>>27)+(c[j>>2]^c[k>>2]^c[l>>2])+(c[m>>2]|0)+(c[g+(c[n>>2]<<2)>>2]|0)+ -899497514;c[m>>2]=c[l>>2];c[l>>2]=c[k>>2];c[k>>2]=c[j>>2]<<30|(c[j>>2]|0)>>>2;c[j>>2]=c[h>>2];c[h>>2]=c[s>>2];c[n>>2]=(c[n>>2]|0)+1}n=c[e>>2]|0;c[n>>2]=(c[n>>2]|0)+t;t=(c[e>>2]|0)+4|0;c[t>>2]=(c[t>>2]|0)+(c[j>>2]|0);j=(c[e>>2]|0)+8|0;c[j>>2]=(c[j>>2]|0)+(c[k>>2]|0);k=(c[e>>2]|0)+12|0;c[k>>2]=(c[k>>2]|0)+(c[l>>2]|0);l=(c[e>>2]|0)+16|0;c[l>>2]=(c[l>>2]|0)+(c[m>>2]|0);i=d;return}function fh(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0;e=i;i=i+96|0;f=e+20|0;g=e+16|0;h=e+12|0;j=e+8|0;k=e+24|0;l=e+4|0;m=e;c[f>>2]=b;c[g>>2]=d;d=c[(c[f>>2]|0)+84>>2]|0;if((c[(c[f>>2]|0)+84>>2]|0)>=56){c[j>>2]=120-d}else{c[j>>2]=56-d}c[l>>2]=c[(c[f>>2]|0)+88>>2]<<3|(c[(c[f>>2]|0)+92>>2]|0)>>>29;c[m>>2]=c[(c[f>>2]|0)+92>>2]<<3;Oh(k|0,0,c[j>>2]|0)|0;a[k]=-128;dh(c[f>>2]|0,k,c[j>>2]|0);a[k]=(c[l>>2]|0)>>>24&255;a[k+1|0]=(c[l>>2]|0)>>>16&255;a[k+2|0]=(c[l>>2]|0)>>>8&255;a[k+3|0]=(c[l>>2]|0)>>>0&255;a[k+4|0]=(c[m>>2]|0)>>>24&255;a[k+5|0]=(c[m>>2]|0)>>>16&255;a[k+6|0]=(c[m>>2]|0)>>>8&255;a[k+7|0]=(c[m>>2]|0)>>>0&255;dh(c[f>>2]|0,k,8);c[h>>2]=0;while(1){if((c[h>>2]|0)>=5){break}a[(c[g>>2]|0)+(c[h>>2]<<2)|0]=(c[(c[f>>2]|0)+(c[h>>2]<<2)>>2]|0)>>>24&255;a[(c[g>>2]|0)+((c[h>>2]<<2)+1)|0]=(c[(c[f>>2]|0)+(c[h>>2]<<2)>>2]|0)>>>16&255;a[(c[g>>2]|0)+((c[h>>2]<<2)+2)|0]=(c[(c[f>>2]|0)+(c[h>>2]<<2)>>2]|0)>>>8&255;a[(c[g>>2]|0)+((c[h>>2]<<2)+3)|0]=c[(c[f>>2]|0)+(c[h>>2]<<2)>>2]&255;c[h>>2]=(c[h>>2]|0)+1}i=e;return}function gh(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0;e=i;i=i+112|0;f=e+104|0;g=e+100|0;h=e+96|0;j=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;bh(j);dh(j,c[f>>2]|0,c[g>>2]|0);fh(j,c[h>>2]|0);i=e;return}function hh(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;g=d;c[e>>2]=a;c[f>>2]=b;c[g>>2]=_f(64)|0;gh(c[e>>2]|0,c[f>>2]|0,c[g>>2]|0);gh(c[g>>2]|0,20,(c[g>>2]|0)+20|0);gh(c[g>>2]|0,40,(c[g>>2]|0)+40|0);c[(c[g>>2]|0)+60>>2]=0;i=d;return c[g>>2]|0}function ih(b,e){b=b|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;f=i;i=i+32|0;g=f+16|0;h=f+12|0;j=f+8|0;k=f+4|0;l=f;c[g>>2]=b;c[h>>2]=e;c[j>>2]=0;c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[h>>2]|0)){break}if((c[(c[g>>2]|0)+60>>2]|0)>=20){c[l>>2]=0;while(1){if((c[l>>2]|0)>=20){break}m=(c[g>>2]|0)+(c[l>>2]|0)|0;if((d[(c[g>>2]|0)+(c[l>>2]|0)|0]|0|0)!=255){n=7;break}a[m]=0;c[l>>2]=(c[l>>2]|0)+1}if((n|0)==7){n=0;a[m]=(a[m]|0)+1<<24>>24}gh(c[g>>2]|0,40,(c[g>>2]|0)+40|0);c[(c[g>>2]|0)+60>>2]=0}e=c[j>>2]<<8;b=(c[g>>2]|0)+60|0;o=c[b>>2]|0;c[b>>2]=o+1;c[j>>2]=e|(d[(c[g>>2]|0)+40+o|0]|0);c[k>>2]=(c[k>>2]|0)+8}c[j>>2]=c[j>>2]&(1<<(c[h>>2]|0)-1<<1)-1;i=f;return c[j>>2]|0}function jh(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0;d=i;i=i+32|0;e=d+20|0;f=d+16|0;g=d+12|0;h=d+8|0;j=d+4|0;k=d;c[e>>2]=a;c[f>>2]=b;c[g>>2]=0;while(1){l=c[g>>2]|0;if(((c[f>>2]|0)>>>(c[g>>2]|0)|0)==0){break}c[g>>2]=l+1}c[g>>2]=l+3;if((c[g>>2]|0)>=32){Ca(5728,5744,275,5760)}c[h>>2]=1<<c[g>>2];c[j>>2]=((c[h>>2]|0)>>>0)/((c[f>>2]|0)>>>0)|0;c[h>>2]=Z(c[f>>2]|0,c[j>>2]|0)|0;do{c[k>>2]=ih(c[e>>2]|0,c[g>>2]|0)|0}while((c[k>>2]|0)>>>0>=(c[h>>2]|0)>>>0);i=d;return((c[k>>2]|0)>>>0)/((c[j>>2]|0)>>>0)|0|0}function kh(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;$f(c[d>>2]|0);i=b;return}function lh(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;c[e>>2]=_f(8)|0;c[c[e>>2]>>2]=0;c[(c[e>>2]|0)+4>>2]=c[d>>2];i=b;return c[e>>2]|0}function mh(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;nh(c[c[d>>2]>>2]|0);$f(c[d>>2]|0);i=b;return}function nh(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[d>>2]|0)==0){i=b;return}nh(c[(c[d>>2]|0)+4>>2]|0);nh(c[(c[d>>2]|0)+8>>2]|0);nh(c[(c[d>>2]|0)+12>>2]|0);nh(c[(c[d>>2]|0)+16>>2]|0);$f(c[d>>2]|0);i=b;return}function oh(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+4|0;e=b;c[e>>2]=a;if((c[c[e>>2]>>2]|0)!=0){c[d>>2]=ph(c[c[e>>2]>>2]|0)|0;f=c[d>>2]|0;i=b;return f|0}else{c[d>>2]=0;f=c[d>>2]|0;i=b;return f|0}return 0}function ph(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0;b=i;i=i+16|0;d=b+12|0;e=b+8|0;f=b+4|0;g=b;c[e>>2]=a;c[f>>2]=0;if((c[e>>2]|0)==0){c[d>>2]=0;h=c[d>>2]|0;i=b;return h|0}c[g>>2]=0;while(1){if((c[g>>2]|0)>=4){break}c[f>>2]=(c[f>>2]|0)+(c[(c[e>>2]|0)+20+(c[g>>2]<<2)>>2]|0);c[g>>2]=(c[g>>2]|0)+1}c[g>>2]=0;while(1){if((c[g>>2]|0)>=3){break}if((c[(c[e>>2]|0)+36+(c[g>>2]<<2)>>2]|0)!=0){c[f>>2]=(c[f>>2]|0)+1}c[g>>2]=(c[g>>2]|0)+1}c[d>>2]=c[f>>2];h=c[d>>2]|0;i=b;return h|0}function qh(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;g=d;c[f>>2]=a;c[g>>2]=b;if((c[(c[f>>2]|0)+4>>2]|0)!=0){c[e>>2]=rh(c[f>>2]|0,c[g>>2]|0,-1)|0;h=c[e>>2]|0;i=d;return h|0}else{c[e>>2]=0;h=c[e>>2]|0;i=d;return h|0}return 0}function rh(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;e=i;i=i+32|0;f=e+28|0;g=e+24|0;h=e+20|0;j=e+16|0;k=e+12|0;l=e+8|0;m=e+4|0;n=e;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[m>>2]=c[h>>2];if((c[c[g>>2]>>2]|0)==0){d=_f(48)|0;c[c[g>>2]>>2]=d;c[(c[c[g>>2]>>2]|0)+44>>2]=0;c[(c[c[g>>2]>>2]|0)+40>>2]=0;c[(c[c[g>>2]>>2]|0)+8>>2]=0;c[(c[c[g>>2]>>2]|0)+4>>2]=0;c[(c[c[g>>2]>>2]|0)+16>>2]=0;c[(c[c[g>>2]>>2]|0)+12>>2]=0;c[(c[c[g>>2]>>2]|0)+24>>2]=0;c[(c[c[g>>2]>>2]|0)+20>>2]=0;c[(c[c[g>>2]>>2]|0)+32>>2]=0;c[(c[c[g>>2]>>2]|0)+28>>2]=0;c[c[c[g>>2]>>2]>>2]=0;c[(c[c[g>>2]>>2]|0)+36>>2]=c[h>>2];c[f>>2]=c[m>>2];o=c[f>>2]|0;i=e;return o|0}c[k>>2]=c[c[g>>2]>>2];a:while(1){if((c[k>>2]|0)==0){p=34;break}do{if((c[j>>2]|0)>=0){d=c[j>>2]|0;if((c[(c[k>>2]|0)+4>>2]|0)==0){c[l>>2]=d;break}if((d|0)<=(c[(c[k>>2]|0)+20>>2]|0)){c[l>>2]=0;break}c[j>>2]=(c[j>>2]|0)-((c[(c[k>>2]|0)+20>>2]|0)+1);if((c[j>>2]|0)<=(c[(c[k>>2]|0)+24>>2]|0)){c[l>>2]=1;break}c[j>>2]=(c[j>>2]|0)-((c[(c[k>>2]|0)+24>>2]|0)+1);if((c[j>>2]|0)<=(c[(c[k>>2]|0)+28>>2]|0)){c[l>>2]=2;break}c[j>>2]=(c[j>>2]|0)-((c[(c[k>>2]|0)+28>>2]|0)+1);if((c[j>>2]|0)>(c[(c[k>>2]|0)+32>>2]|0)){p=16;break a}c[l>>2]=3}else{d=Qb[c[(c[g>>2]|0)+4>>2]&15](c[h>>2]|0,c[(c[k>>2]|0)+36>>2]|0)|0;c[n>>2]=d;if((d|0)<0){c[l>>2]=0;break}q=(c[k>>2]|0)+36|0;if((c[n>>2]|0)==0){p=20;break a}if((c[q+4>>2]|0)!=0?(d=Qb[c[(c[g>>2]|0)+4>>2]&15](c[h>>2]|0,c[(c[k>>2]|0)+40>>2]|0)|0,c[n>>2]=d,(d|0)>=0):0){r=(c[k>>2]|0)+36|0;if((c[n>>2]|0)==0){p=25;break a}if((c[r+8>>2]|0)!=0?(d=Qb[c[(c[g>>2]|0)+4>>2]&15](c[h>>2]|0,c[(c[k>>2]|0)+44>>2]|0)|0,c[n>>2]=d,(d|0)>=0):0){if((c[n>>2]|0)==0){p=30;break a}c[l>>2]=3;break}c[l>>2]=2;break}c[l>>2]=1}}while(0);if((c[(c[k>>2]|0)+4+(c[l>>2]<<2)>>2]|0)==0){p=34;break}c[k>>2]=c[(c[k>>2]|0)+4+(c[l>>2]<<2)>>2]}if((p|0)==16){c[f>>2]=0;o=c[f>>2]|0;i=e;return o|0}else if((p|0)==20){c[f>>2]=c[q>>2];o=c[f>>2]|0;i=e;return o|0}else if((p|0)==25){c[f>>2]=c[r+4>>2];o=c[f>>2]|0;i=e;return o|0}else if((p|0)==30){c[f>>2]=c[(c[k>>2]|0)+44>>2];o=c[f>>2]|0;i=e;return o|0}else if((p|0)==34){Ah(0,c[h>>2]|0,0,c[g>>2]|0,c[k>>2]|0,c[l>>2]|0)|0;c[f>>2]=c[m>>2];o=c[f>>2]|0;i=e;return o|0}return 0}function sh(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0;d=i;i=i+16|0;e=d+12|0;f=d+8|0;g=d+4|0;h=d;c[f>>2]=a;c[g>>2]=b;if((c[c[f>>2]>>2]|0)==0){c[e>>2]=0;j=c[e>>2]|0;i=d;return j|0}if((c[g>>2]|0)>=0?(b=c[g>>2]|0,(b|0)<(ph(c[c[f>>2]>>2]|0)|0)):0){c[h>>2]=c[c[f>>2]>>2];while(1){if((c[h>>2]|0)==0){k=21;break}f=c[h>>2]|0;if((c[g>>2]|0)<(c[(c[h>>2]|0)+20>>2]|0)){c[h>>2]=c[f+4>>2];continue}c[g>>2]=(c[g>>2]|0)-((c[f+20>>2]|0)+1);if((c[g>>2]|0)<0){k=11;break}f=c[h>>2]|0;if((c[g>>2]|0)<(c[(c[h>>2]|0)+24>>2]|0)){c[h>>2]=c[f+8>>2];continue}c[g>>2]=(c[g>>2]|0)-((c[f+24>>2]|0)+1);if((c[g>>2]|0)<0){k=15;break}f=c[h>>2]|0;if((c[g>>2]|0)<(c[(c[h>>2]|0)+28>>2]|0)){c[h>>2]=c[f+12>>2];continue}c[g>>2]=(c[g>>2]|0)-((c[f+28>>2]|0)+1);l=c[h>>2]|0;if((c[g>>2]|0)<0){k=19;break}c[h>>2]=c[l+16>>2]}if((k|0)==11){c[e>>2]=c[(c[h>>2]|0)+36>>2];j=c[e>>2]|0;i=d;return j|0}else if((k|0)==15){c[e>>2]=c[(c[h>>2]|0)+40>>2];j=c[e>>2]|0;i=d;return j|0}else if((k|0)==19){c[e>>2]=c[l+44>>2];j=c[e>>2]|0;i=d;return j|0}else if((k|0)==21){c[e>>2]=0;j=c[e>>2]|0;i=d;return j|0}}c[e>>2]=0;j=c[e>>2]|0;i=d;return j|0}function th(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0;g=i;i=i+64|0;h=g+48|0;j=g+44|0;k=g+40|0;l=g+36|0;m=g+32|0;n=g+28|0;o=g+24|0;p=g+20|0;q=g+16|0;r=g+12|0;s=g+8|0;t=g+4|0;u=g;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=f;if((c[c[j>>2]>>2]|0)==0){c[h>>2]=0;v=c[h>>2]|0;i=g;return v|0}if((c[l>>2]|0)==0){c[l>>2]=c[(c[j>>2]|0)+4>>2]}c[o>>2]=c[c[j>>2]>>2];c[r>>2]=0;c[s>>2]=-1;c[u>>2]=0;do{if((c[k>>2]|0)==0){if(!((c[m>>2]|0)==1|(c[m>>2]|0)==3)){Ca(5776,5824,471,5840)}if((c[m>>2]|0)==1){c[u>>2]=1;break}if((c[m>>2]|0)==3){c[u>>2]=-1}}}while(0);while(1){c[t>>2]=0;while(1){if((c[t>>2]|0)>=4|(c[t>>2]|0)>=3){break}if((c[(c[o>>2]|0)+36+(c[t>>2]<<2)>>2]|0)==0){break}if((c[u>>2]|0)!=0){w=c[u>>2]|0}else{w=Qb[c[l>>2]&15](c[k>>2]|0,c[(c[o>>2]|0)+36+(c[t>>2]<<2)>>2]|0)|0}c[q>>2]=w;if((w|0)<0){break}if((c[(c[o>>2]|0)+4+(c[t>>2]<<2)>>2]|0)!=0){c[r>>2]=(c[r>>2]|0)+(c[(c[o>>2]|0)+20+(c[t>>2]<<2)>>2]|0)}if((c[q>>2]|0)==0){x=22;break}c[r>>2]=(c[r>>2]|0)+1;c[t>>2]=(c[t>>2]|0)+1}if((x|0)==22){x=0;c[s>>2]=c[t>>2]}if((c[s>>2]|0)>=0){break}if((c[(c[o>>2]|0)+4+(c[t>>2]<<2)>>2]|0)==0){break}c[o>>2]=c[(c[o>>2]|0)+4+(c[t>>2]<<2)>>2]}t=c[m>>2]|0;do{if((c[s>>2]|0)<0){if((t|0)==0){c[h>>2]=0;v=c[h>>2]|0;i=g;return v|0}else{if(!((c[m>>2]|0)==1|(c[m>>2]|0)==2)){break}c[r>>2]=(c[r>>2]|0)+ -1;break}}else{if(!((t|0)!=1&(c[m>>2]|0)!=3)){x=c[r>>2]|0;if((c[m>>2]|0)==1){c[r>>2]=x+ -1;break}else{c[r>>2]=x+1;break}}if((c[n>>2]|0)!=0){c[c[n>>2]>>2]=c[r>>2]}c[h>>2]=c[(c[o>>2]|0)+36+(c[s>>2]<<2)>>2];v=c[h>>2]|0;i=g;return v|0}}while(0);c[p>>2]=sh(c[j>>2]|0,c[r>>2]|0)|0;if((c[p>>2]|0)!=0?(c[n>>2]|0)!=0:0){c[c[n>>2]>>2]=c[r>>2]}c[h>>2]=c[p>>2];v=c[h>>2]|0;i=g;return v|0}



function Tb(a){a=a|0;var b=0;b=i;i=i+a|0;i=i+7&-8;return b|0}function Ub(){return i|0}function Vb(a){a=a|0;i=a}function Wb(a,b){a=a|0;b=b|0;if((m|0)==0){m=a;n=b}}function Xb(b){b=b|0;a[k]=a[b];a[k+1|0]=a[b+1|0];a[k+2|0]=a[b+2|0];a[k+3|0]=a[b+3|0]}function Yb(b){b=b|0;a[k]=a[b];a[k+1|0]=a[b+1|0];a[k+2|0]=a[b+2|0];a[k+3|0]=a[b+3|0];a[k+4|0]=a[b+4|0];a[k+5|0]=a[b+5|0];a[k+6|0]=a[b+6|0];a[k+7|0]=a[b+7|0]}function Zb(a){a=a|0;B=a}function _b(a){a=a|0;C=a}function $b(a){a=a|0;D=a}function ac(a){a=a|0;E=a}function bc(a){a=a|0;F=a}function cc(a){a=a|0;G=a}function dc(a){a=a|0;H=a}function ec(a){a=a|0;I=a}function fc(a){a=a|0;J=a}function gc(a){a=a|0;K=a}function hc(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,h=0,j=0,k=0;e=i;i=i+16|0;f=e+12|0;h=e+8|0;j=e+4|0;k=e;c[f>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=_f(32)|0;c[c[k>>2]>>2]=c[f>>2];c[(c[k>>2]|0)+4>>2]=c[j>>2];c[(c[k>>2]|0)+8>>2]=0;c[(c[k>>2]|0)+16>>2]=0;c[(c[k>>2]|0)+12>>2]=0;g[(c[k>>2]|0)+20>>2]=1.0;c[(c[k>>2]|0)+24>>2]=c[h>>2];c[(c[k>>2]|0)+28>>2]=0;i=e;return c[k>>2]|0}function ic(a,b,d,e,f,g,h,j){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;k=i;i=i+32|0;l=k+28|0;m=k+24|0;n=k+20|0;o=k+16|0;p=k+12|0;q=k+8|0;r=k+4|0;s=k;c[l>>2]=a;c[m>>2]=b;c[n>>2]=d;c[o>>2]=e;c[p>>2]=f;c[q>>2]=g;c[r>>2]=h;c[s>>2]=j;Ob[c[c[c[l>>2]>>2]>>2]&1](c[(c[l>>2]|0)+4>>2]|0,c[m>>2]|0,c[n>>2]|0,c[o>>2]|0,c[p>>2]|0,c[q>>2]|0,c[r>>2]|0,c[s>>2]|0);i=k;return}function jc(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0;h=i;i=i+32|0;j=h+20|0;k=h+16|0;l=h+12|0;m=h+8|0;n=h+4|0;o=h;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=f;c[o>>2]=g;Pb[c[(c[c[j>>2]>>2]|0)+4>>2]&3](c[(c[j>>2]|0)+4>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0,c[n>>2]|0,c[o>>2]|0);i=h;return}function kc(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0;h=i;i=i+32|0;j=h+20|0;k=h+16|0;l=h+12|0;m=h+8|0;n=h+4|0;o=h;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=f;c[o>>2]=g;Pb[c[(c[c[j>>2]>>2]|0)+8>>2]&3](c[(c[j>>2]|0)+4>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0,c[n>>2]|0,c[o>>2]|0);i=h;return}function lc(a,b,d,e,f,h,j){a=a|0;b=+b;d=+d;e=+e;f=+f;h=+h;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0;k=i;i=i+80|0;l=k+68|0;m=k+64|0;n=k+60|0;o=k+56|0;p=k+52|0;q=k+48|0;r=k+44|0;s=k+40|0;t=k+36|0;u=k+32|0;v=k;c[l>>2]=a;g[m>>2]=b;g[n>>2]=d;g[o>>2]=e;g[p>>2]=f;g[q>>2]=h;c[r>>2]=j;if((c[(c[c[l>>2]>>2]|0)+96>>2]|0)!=0){Jb[c[(c[c[l>>2]>>2]|0)+96>>2]&1](c[(c[l>>2]|0)+4>>2]|0,+g[m>>2],+g[n>>2],+g[o>>2],+g[p>>2],+g[q>>2],c[r>>2]|0);i=k;return}else{g[s>>2]=+N(+((+g[p>>2]- +g[n>>2])*(+g[p>>2]- +g[n>>2])+(+g[q>>2]- +g[o>>2])*(+g[q>>2]- +g[o>>2])));g[t>>2]=(+g[p>>2]- +g[n>>2])/+g[s>>2]*(+g[m>>2]/2.0-.2);g[u>>2]=(+g[q>>2]- +g[o>>2])/+g[s>>2]*(+g[m>>2]/2.0-.2);c[v>>2]=~~(+g[n>>2]- +g[u>>2]);c[v+4>>2]=~~(+g[o>>2]+ +g[t>>2]);c[v+8>>2]=~~(+g[p>>2]- +g[u>>2]);c[v+12>>2]=~~(+g[q>>2]+ +g[t>>2]);c[v+16>>2]=~~(+g[p>>2]+ +g[u>>2]);c[v+20>>2]=~~(+g[q>>2]- +g[t>>2]);c[v+24>>2]=~~(+g[n>>2]+ +g[u>>2]);c[v+28>>2]=~~(+g[o>>2]- +g[t>>2]);Eb[c[(c[c[l>>2]>>2]|0)+12>>2]&31](c[(c[l>>2]|0)+4>>2]|0,v,4,c[r>>2]|0,c[r>>2]|0);i=k;return}}function mc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0;g=i;i=i+32|0;h=g+16|0;j=g+12|0;k=g+8|0;l=g+4|0;m=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;Eb[c[(c[c[h>>2]>>2]|0)+12>>2]&31](c[(c[h>>2]|0)+4>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0);i=g;return}function nc(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0;h=i;i=i+32|0;j=h+20|0;k=h+16|0;l=h+12|0;m=h+8|0;n=h+4|0;o=h;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=f;c[o>>2]=g;Pb[c[(c[c[j>>2]>>2]|0)+16>>2]&3](c[(c[j>>2]|0)+4>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0,c[n>>2]|0,c[o>>2]|0);i=h;return}function oc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0;g=i;i=i+32|0;h=g+16|0;j=g+12|0;k=g+8|0;l=g+4|0;m=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;if((c[(c[c[h>>2]>>2]|0)+20>>2]|0)==0){i=g;return}Eb[c[(c[c[h>>2]>>2]|0)+20>>2]&31](c[(c[h>>2]|0)+4>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0);i=g;return}function pc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0;g=i;i=i+32|0;h=g+16|0;j=g+12|0;k=g+8|0;l=g+4|0;m=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;Eb[c[(c[c[h>>2]>>2]|0)+24>>2]&31](c[(c[h>>2]|0)+4>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0);i=g;return}function qc(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;Gb[c[(c[c[d>>2]>>2]|0)+28>>2]&7](c[(c[d>>2]|0)+4>>2]|0);i=b;return}function rc(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;Gb[c[(c[c[d>>2]>>2]|0)+32>>2]&7](c[(c[d>>2]|0)+4>>2]|0);i=b;return}function sc(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;Gb[c[(c[c[d>>2]>>2]|0)+36>>2]&7](c[(c[d>>2]|0)+4>>2]|0);i=b;return}function tc(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;g=d;c[e>>2]=a;c[f>>2]=b;if((c[(c[c[e>>2]>>2]|0)+40>>2]|0)==0){i=d;return}if((c[(c[e>>2]|0)+24>>2]|0)==0){Ca(24,8,198,32)}c[g>>2]=Ig(c[(c[e>>2]|0)+24>>2]|0,c[f>>2]|0)|0;if((c[(c[e>>2]|0)+28>>2]|0)!=0?(Lh(c[g>>2]|0,c[(c[e>>2]|0)+28>>2]|0)|0)==0:0){$f(c[g>>2]|0);i=d;return}Hb[c[(c[c[e>>2]>>2]|0)+40>>2]&7](c[(c[e>>2]|0)+4>>2]|0,c[g>>2]|0);$f(c[(c[e>>2]|0)+28>>2]|0);c[(c[e>>2]|0)+28>>2]=c[g>>2];i=d;return}function uc(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;b=vc(c[e>>2]|0,+(c[f>>2]|0),+(c[f>>2]|0),+(c[f>>2]|0),+(c[f>>2]|0),-1,0)|0;i=d;return b|0}function vc(a,b,d,e,f,h,j){a=a|0;b=+b;d=+d;e=+e;f=+f;h=h|0;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;k=i;i=i+32|0;l=k+24|0;m=k+20|0;n=k+16|0;o=k+12|0;p=k+8|0;q=k+4|0;r=k;c[l>>2]=a;g[m>>2]=b;g[n>>2]=d;g[o>>2]=e;g[p>>2]=f;c[q>>2]=h;c[r>>2]=j;if((c[(c[l>>2]|0)+12>>2]|0)>=(c[(c[l>>2]|0)+16>>2]|0)){c[(c[l>>2]|0)+16>>2]=(c[(c[l>>2]|0)+12>>2]|0)+16;j=ag(c[(c[l>>2]|0)+8>>2]|0,(c[(c[l>>2]|0)+16>>2]|0)*24|0)|0;c[(c[l>>2]|0)+8>>2]=j}c[(c[(c[l>>2]|0)+8>>2]|0)+((c[(c[l>>2]|0)+12>>2]|0)*24|0)>>2]=c[q>>2];c[(c[(c[l>>2]|0)+8>>2]|0)+((c[(c[l>>2]|0)+12>>2]|0)*24|0)+4>>2]=c[r>>2];g[(c[(c[l>>2]|0)+8>>2]|0)+((c[(c[l>>2]|0)+12>>2]|0)*24|0)+8>>2]=+g[m>>2];g[(c[(c[l>>2]|0)+8>>2]|0)+((c[(c[l>>2]|0)+12>>2]|0)*24|0)+12>>2]=+g[n>>2];g[(c[(c[l>>2]|0)+8>>2]|0)+((c[(c[l>>2]|0)+12>>2]|0)*24|0)+16>>2]=+g[o>>2];g[(c[(c[l>>2]|0)+8>>2]|0)+((c[(c[l>>2]|0)+12>>2]|0)*24|0)+20>>2]=+g[p>>2];p=(c[l>>2]|0)+12|0;l=c[p>>2]|0;c[p>>2]=l+1;i=k;return l|0}function wc(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;g=d;c[e>>2]=a;c[f>>2]=b;c[g>>2]=0;while(1){if((c[g>>2]|0)>=(c[f>>2]|0)){break}c[(c[e>>2]|0)+(c[g>>2]<<2)>>2]=6;c[g>>2]=(c[g>>2]|0)+1}i=d;return}function xc(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;c[e>>2]=_f(c[d>>2]<<2)|0;wc(c[e>>2]|0,c[d>>2]|0);i=b;return c[e>>2]|0}function yc(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;b=zc(c[e>>2]|0,c[f>>2]|0,0)|0;i=d;return b|0}function zc(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;e=i;i=i+32|0;f=e+28|0;g=e+24|0;h=e+20|0;j=e+16|0;k=e+12|0;l=e+8|0;m=e+4|0;n=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;c[j>>2]=c[g>>2];c[l>>2]=0;if((c[g>>2]|0)<0){Ca(48,64,110,72)}while(1){o=c[g>>2]|0;if((c[(c[f>>2]|0)+(c[g>>2]<<2)>>2]&2|0)!=0){break}c[l>>2]=c[l>>2]^c[(c[f>>2]|0)+(o<<2)>>2]&1;c[g>>2]=c[(c[f>>2]|0)+(c[g>>2]<<2)>>2]>>2}c[k>>2]=o;if((c[h>>2]|0)!=0){c[c[h>>2]>>2]=c[l>>2]}c[g>>2]=c[j>>2];while(1){if((c[g>>2]|0)==(c[k>>2]|0)){break}c[m>>2]=c[(c[f>>2]|0)+(c[g>>2]<<2)>>2]>>2;c[n>>2]=c[l>>2]^c[(c[f>>2]|0)+(c[g>>2]<<2)>>2]&1;c[(c[f>>2]|0)+(c[g>>2]<<2)>>2]=c[k>>2]<<2|c[l>>2];c[l>>2]=c[n>>2];c[g>>2]=c[m>>2]}if((c[l>>2]|0)==0){i=e;return c[g>>2]|0}else{Ca(88,64,137,72)}return 0}function Ac(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0;e=i;i=i+16|0;f=e+8|0;g=e+4|0;h=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;Bc(c[f>>2]|0,c[g>>2]|0,c[h>>2]|0,0);i=e;return}function Bc(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;f=i;i=i+32|0;g=f+24|0;h=f+20|0;j=f+16|0;k=f+12|0;l=f+8|0;m=f+4|0;n=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[h>>2]=zc(c[g>>2]|0,c[h>>2]|0,l)|0;if((c[(c[g>>2]|0)+(c[h>>2]<<2)>>2]&2|0)==0){Ca(104,64,152,120)}c[k>>2]=c[k>>2]^c[l>>2];c[j>>2]=zc(c[g>>2]|0,c[j>>2]|0,m)|0;if((c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]&2|0)==0){Ca(136,64,155,120)}c[k>>2]=c[k>>2]^c[m>>2];l=c[k>>2]|0;do{if((c[h>>2]|0)==(c[j>>2]|0)){if((l|0)!=0){Ca(152,64,161,120)}else{break}}else{if(!((l|0)==0|(c[k>>2]|0)==1)){Ca(168,64,163,120)}if((c[h>>2]|0)>(c[j>>2]|0)){c[n>>2]=c[h>>2];c[h>>2]=c[j>>2];c[j>>2]=c[n>>2]}e=(c[g>>2]|0)+(c[h>>2]<<2)|0;c[e>>2]=(c[e>>2]|0)+(c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]>>2<<2);c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]=c[h>>2]<<2|((c[k>>2]|0)!=0^1^1)&1}}while(0);c[j>>2]=zc(c[g>>2]|0,c[j>>2]|0,m)|0;if((c[j>>2]|0)!=(c[h>>2]|0)){Ca(200,64,188,120)}if((c[m>>2]|0)==(c[k>>2]|0)){i=f;return}else{Ca(216,64,189,120)}}function Cc(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;b=yc(c[e>>2]|0,c[f>>2]|0)|0;i=d;return c[(c[e>>2]|0)+(b<<2)>>2]>>2|0}function Dc(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;if((c[(c[d>>2]|0)+44>>2]|0)==0){Ca(232,248,33,256)}a=(c[d>>2]|0)+44|0;c[a>>2]=(c[a>>2]|0)+ -1;if((c[(c[d>>2]|0)+44>>2]|0)!=0){i=b;return}c[e>>2]=0;while(1){if((c[e>>2]|0)>=(c[c[d>>2]>>2]|0)){break}$f(c[(c[(c[d>>2]|0)+4>>2]|0)+((c[e>>2]|0)*24|0)+8>>2]|0);$f(c[(c[(c[d>>2]|0)+4>>2]|0)+((c[e>>2]|0)*24|0)+4>>2]|0);c[e>>2]=(c[e>>2]|0)+1}c[e>>2]=0;while(1){if((c[e>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){break}$f(c[(c[(c[d>>2]|0)+20>>2]|0)+((c[e>>2]|0)*20|0)+8>>2]|0);$f(c[(c[(c[d>>2]|0)+20>>2]|0)+((c[e>>2]|0)*20|0)+4>>2]|0);c[e>>2]=(c[e>>2]|0)+1}$f(c[(c[d>>2]|0)+4>>2]|0);$f(c[(c[d>>2]|0)+12>>2]|0);$f(c[(c[d>>2]|0)+20>>2]|0);$f(c[d>>2]|0);i=b;return}function Ec(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;e=i;i=i+64|0;f=e+48|0;g=e+44|0;j=e+40|0;k=e+36|0;l=e+8|0;m=e+32|0;n=e+28|0;o=e+24|0;p=e+20|0;q=e+16|0;r=e;c[f>>2]=a;c[g>>2]=b;c[j>>2]=d;h[l>>3]=0.0;c[k>>2]=0;c[m>>2]=0;while(1){if((c[m>>2]|0)>=(c[(c[f>>2]|0)+8>>2]|0)){break}c[n>>2]=(c[(c[f>>2]|0)+12>>2]|0)+(c[m>>2]<<4);d=Z((c[(c[c[n>>2]>>2]|0)+12>>2]|0)-(c[(c[(c[n>>2]|0)+4>>2]|0)+12>>2]|0)|0,(c[(c[c[n>>2]>>2]|0)+12>>2]|0)-(c[(c[(c[n>>2]|0)+4>>2]|0)+12>>2]|0)|0)|0;c[o>>2]=d+(Z((c[(c[c[n>>2]>>2]|0)+16>>2]|0)-(c[(c[(c[n>>2]|0)+4>>2]|0)+16>>2]|0)|0,(c[(c[c[n>>2]>>2]|0)+16>>2]|0)-(c[(c[(c[n>>2]|0)+4>>2]|0)+16>>2]|0)|0)|0);d=Z((c[(c[c[n>>2]>>2]|0)+12>>2]|0)-(c[g>>2]|0)|0,(c[(c[c[n>>2]>>2]|0)+12>>2]|0)-(c[g>>2]|0)|0)|0;c[p>>2]=d+(Z((c[(c[c[n>>2]>>2]|0)+16>>2]|0)-(c[j>>2]|0)|0,(c[(c[c[n>>2]>>2]|0)+16>>2]|0)-(c[j>>2]|0)|0)|0);d=Z((c[(c[(c[n>>2]|0)+4>>2]|0)+12>>2]|0)-(c[g>>2]|0)|0,(c[(c[(c[n>>2]|0)+4>>2]|0)+12>>2]|0)-(c[g>>2]|0)|0)|0;c[q>>2]=d+(Z((c[(c[(c[n>>2]|0)+4>>2]|0)+16>>2]|0)-(c[j>>2]|0)|0,(c[(c[(c[n>>2]|0)+4>>2]|0)+16>>2]|0)-(c[j>>2]|0)|0)|0);do{if(((c[p>>2]|0)<((c[o>>2]|0)+(c[q>>2]|0)|0)?(c[q>>2]|0)<((c[o>>2]|0)+(c[p>>2]|0)|0):0)?(h[r>>3]=+Fc(c[g>>2]|0,c[j>>2]|0,c[(c[c[n>>2]>>2]|0)+12>>2]|0,c[(c[c[n>>2]>>2]|0)+16>>2]|0,c[(c[(c[n>>2]|0)+4>>2]|0)+12>>2]|0,c[(c[(c[n>>2]|0)+4>>2]|0)+16>>2]|0),!(+h[r>>3]*+h[r>>3]*4.0>+(c[o>>2]|0))):0){if((c[k>>2]|0)!=0?!(+h[r>>3]<+h[l>>3]):0){break}c[k>>2]=c[n>>2];h[l>>3]=+h[r>>3]}}while(0);c[m>>2]=(c[m>>2]|0)+1}i=e;return c[k>>2]|0}function Fc(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;j=i;i=i+48|0;k=j+32|0;l=j+28|0;m=j+24|0;n=j+20|0;o=j+16|0;p=j+12|0;q=j+8|0;r=j;c[k>>2]=a;c[l>>2]=b;c[m>>2]=d;c[n>>2]=e;c[o>>2]=f;c[p>>2]=g;g=Z(c[m>>2]|0,c[p>>2]|0)|0;f=g-(Z(c[o>>2]|0,c[n>>2]|0)|0)|0;g=f+(Z(c[o>>2]|0,c[l>>2]|0)|0)|0;f=g-(Z(c[k>>2]|0,c[p>>2]|0)|0)|0;g=f+(Z(c[k>>2]|0,c[n>>2]|0)|0)|0;c[q>>2]=g-(Z(c[m>>2]|0,c[l>>2]|0)|0);l=c[q>>2]|0;c[q>>2]=(c[q>>2]|0)>(0-(c[q>>2]|0)|0)?l:0-l|0;l=Z((c[m>>2]|0)-(c[o>>2]|0)|0,(c[m>>2]|0)-(c[o>>2]|0)|0)|0;h[r>>3]=+N(+(+(l+(Z((c[n>>2]|0)-(c[p>>2]|0)|0,(c[n>>2]|0)-(c[p>>2]|0)|0)|0)|0)));i=j;return+(+(c[q>>2]|0)/+h[r>>3])}function Gc(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0,L=0,O=0,P=0,Q=0,R=0,S=0,T=0,U=0,V=0,W=0,X=0,Y=0,_=0,$=0,aa=0,ba=0,ca=0,da=0,ea=0,fa=0,ga=0,ha=0,ia=0,ja=0,ka=0,la=0,ma=0,na=0,oa=0,pa=0,qa=0,ra=0,sa=0,ta=0,ua=0,va=0,wa=0,xa=0,ya=0,za=0,Aa=0,Ba=0,Da=0,Ea=0,Fa=0,Ga=0,Ha=0,Ia=0,Ja=0,Ka=0,La=0,Ma=0,Na=0,Oa=0,Pa=0,Qa=0,Ra=0,Sa=0,Ta=0,Ua=0,Va=0,Wa=0,Xa=0,Ya=0,Za=0,_a=0,$a=0,ab=0,bb=0,cb=0,db=0,eb=0,fb=0,gb=0.0,hb=0;b=i;i=i+896|0;d=b+884|0;e=b+608|0;f=b+600|0;g=b+592|0;j=b+880|0;k=b+876|0;l=b+872|0;m=b+868|0;n=b+856|0;o=b+844|0;p=b+832|0;q=b+828|0;s=b+824|0;t=b+576|0;u=b+560|0;v=b+820|0;w=b+488|0;x=b+464|0;y=b+440|0;z=b+816|0;A=b+812|0;B=b+808|0;C=b+804|0;D=b+800|0;E=b+796|0;F=b+792|0;G=b+376|0;H=b+352|0;I=b+336|0;J=b+320|0;K=b+304|0;L=b+280|0;O=b+272|0;P=b+788|0;Q=b+784|0;R=b+780|0;S=b+776|0;T=b+772|0;U=b+768|0;V=b+264|0;W=b+248|0;X=b+232|0;Y=b+216|0;_=b+192|0;$=b+184|0;aa=b+176|0;ba=b+764|0;ca=b+760|0;da=b+756|0;ea=b+752|0;fa=b+748|0;ga=b+744|0;ha=b+168|0;ia=b+740|0;ja=b+736|0;ka=b+732|0;la=b+728|0;ma=b+724|0;na=b+720|0;oa=b+160|0;pa=b+152|0;qa=b+120|0;ra=b+104|0;sa=b+88|0;ta=b+716|0;ua=b+712|0;va=b+708|0;wa=b+704|0;xa=b+700|0;ya=b+696|0;za=b+692|0;Aa=b+80|0;Ba=b+72|0;Da=b+688|0;Ea=b+684|0;Fa=b+680|0;Ga=b+676|0;Ha=b+672|0;Ia=b+668|0;Ja=b+664|0;Ka=b+660|0;La=b+64|0;Ma=b+656|0;Na=b+652|0;Oa=b+648|0;Pa=b+644|0;Qa=b+56|0;Ra=b+48|0;Sa=b+40|0;Ta=b+640|0;Ua=b+636|0;Va=b+632|0;Wa=b+628|0;Xa=b+624|0;Ya=b+620|0;Za=b+32|0;_a=b+24|0;$a=b+16|0;ab=b+616|0;bb=b+8|0;cb=b;c[d>>2]=a;if((c[(c[d>>2]|0)+12>>2]|0)!=0){i=b;return}c[s>>2]=0;c[q>>2]=0;h[g>>3]=0.0;h[f>>3]=0.0;h[e>>3]=0.0;c[j>>2]=0;while(1){if(((c[j>>2]|0)+2|0)>=(c[c[d>>2]>>2]<<1|0)){break}a=c[j>>2]|0;db=c[d>>2]|0;if((c[j>>2]|0)<(c[c[d>>2]>>2]|0)){c[n+(c[q>>2]<<2)>>2]=c[(c[db+8>>2]|0)+(a<<2)>>2];eb=c[(c[(c[d>>2]|0)+8>>2]|0)+((((c[j>>2]|0)+1|0)%(c[c[d>>2]>>2]|0)|0)<<2)>>2]|0;fb=c[q>>2]|0;c[q>>2]=fb+1;c[o+(fb<<2)>>2]=eb}else{eb=c[(c[(c[d>>2]|0)+8>>2]|0)+(a-(c[db>>2]|0)<<2)>>2]|0;db=c[s>>2]|0;c[s>>2]=db+1;c[p+(db<<2)>>2]=eb}c[k>>2]=(c[j>>2]|0)+1;while(1){if(((c[k>>2]|0)+1|0)>=(c[c[d>>2]>>2]<<1|0)){break}eb=c[k>>2]|0;db=c[d>>2]|0;if((c[k>>2]|0)<(c[c[d>>2]>>2]|0)){c[n+(c[q>>2]<<2)>>2]=c[(c[db+8>>2]|0)+(eb<<2)>>2];a=c[(c[(c[d>>2]|0)+8>>2]|0)+((((c[k>>2]|0)+1|0)%(c[c[d>>2]>>2]|0)|0)<<2)>>2]|0;fb=c[q>>2]|0;c[q>>2]=fb+1;c[o+(fb<<2)>>2]=a}else{a=c[(c[(c[d>>2]|0)+8>>2]|0)+(eb-(c[db>>2]|0)<<2)>>2]|0;db=c[s>>2]|0;c[s>>2]=db+1;c[p+(db<<2)>>2]=a}c[l>>2]=(c[k>>2]|0)+1;while(1){if((c[l>>2]|0)>=(c[c[d>>2]>>2]<<1|0)){break}c[v>>2]=0;a=c[l>>2]|0;db=c[d>>2]|0;if((c[l>>2]|0)<(c[c[d>>2]>>2]|0)){c[n+(c[q>>2]<<2)>>2]=c[(c[db+8>>2]|0)+(a<<2)>>2];eb=c[(c[(c[d>>2]|0)+8>>2]|0)+((((c[l>>2]|0)+1|0)%(c[c[d>>2]>>2]|0)|0)<<2)>>2]|0;fb=c[q>>2]|0;c[q>>2]=fb+1;c[o+(fb<<2)>>2]=eb}else{eb=c[(c[(c[d>>2]|0)+8>>2]|0)+(a-(c[db>>2]|0)<<2)>>2]|0;db=c[s>>2]|0;c[s>>2]=db+1;c[p+(db<<2)>>2]=eb}do{if((c[q>>2]|0)==3){c[z>>2]=0;while(1){if((c[z>>2]|0)>=3){break}c[A>>2]=c[(c[n+(c[z>>2]<<2)>>2]|0)+12>>2];c[B>>2]=c[(c[o+(c[z>>2]<<2)>>2]|0)+12>>2];c[C>>2]=c[(c[n+(c[z>>2]<<2)>>2]|0)+16>>2];c[D>>2]=c[(c[o+(c[z>>2]<<2)>>2]|0)+16>>2];c[E>>2]=(c[B>>2]|0)-(c[A>>2]|0);c[F>>2]=(c[D>>2]|0)-(c[C>>2]|0);h[w+(((c[z>>2]|0)*3|0)+0<<3)>>3]=+(c[F>>2]|0);h[w+(((c[z>>2]|0)*3|0)+1<<3)>>3]=+(0-(c[E>>2]|0)|0);gb=-+N(+(+(c[E>>2]|0)*+(c[E>>2]|0)+ +(c[F>>2]|0)*+(c[F>>2]|0)));h[w+(((c[z>>2]|0)*3|0)+2<<3)>>3]=gb;h[x+(c[z>>2]<<3)>>3]=+(c[A>>2]|0)*+(c[F>>2]|0)- +(c[C>>2]|0)*+(c[E>>2]|0);c[z>>2]=(c[z>>2]|0)+1}if((Hc(w,x,y)|0)!=0){h[t+(c[v>>2]<<3)>>3]=+h[y>>3];h[u+(c[v>>2]<<3)>>3]=+h[y+8>>3];c[v>>2]=(c[v>>2]|0)+1}}else{if((c[q>>2]|0)==2){c[m>>2]=0;while(1){if((c[m>>2]|0)>=2){break}c[P>>2]=c[(c[n+(c[m>>2]<<2)>>2]|0)+12>>2];c[Q>>2]=c[(c[o+(c[m>>2]<<2)>>2]|0)+12>>2];c[R>>2]=c[(c[n+(c[m>>2]<<2)>>2]|0)+16>>2];c[S>>2]=c[(c[o+(c[m>>2]<<2)>>2]|0)+16>>2];c[T>>2]=(c[Q>>2]|0)-(c[P>>2]|0);c[U>>2]=(c[S>>2]|0)-(c[R>>2]|0);h[G+(c[m>>2]<<5)>>3]=+(c[U>>2]|0);h[G+(c[m>>2]<<5)+8>>3]=+(0-(c[T>>2]|0)|0);eb=Z(c[T>>2]|0,c[T>>2]|0)|0;gb=-+N(+(+(eb+(Z(c[U>>2]|0,c[U>>2]|0)|0)|0)));h[G+(c[m>>2]<<5)+16>>3]=gb;eb=Z(c[P>>2]|0,c[U>>2]|0)|0;gb=+(eb-(Z(c[R>>2]|0,c[T>>2]|0)|0)|0);h[G+(c[m>>2]<<5)+24>>3]=gb;c[m>>2]=(c[m>>2]|0)+1}h[H>>3]=+h[G>>3]*+h[G+48>>3]- +h[G+32>>3]*+h[G+16>>3];h[H+8>>3]=+h[G+8>>3]*+h[G+48>>3]- +h[G+40>>3]*+h[G+16>>3];h[H+16>>3]=+h[G+24>>3]*+h[G+48>>3]- +h[G+56>>3]*+h[G+16>>3];gb=+M(+(+h[H>>3]));if(gb<+M(+(+h[H+8>>3]))){h[I>>3]=1.0;h[I+8>>3]=0.0;h[J>>3]=-+h[H>>3]/+h[H+8>>3];h[J+8>>3]=+h[H+16>>3]/+h[H+8>>3]}else{h[J>>3]=1.0;h[J+8>>3]=0.0;h[I>>3]=-+h[H+8>>3]/+h[H>>3];h[I+8>>3]=+h[H+16>>3]/+h[H>>3]}h[K>>3]=-(+h[G>>3]*+h[I>>3]+ +h[G+8>>3]*+h[J>>3])/+h[G+16>>3];h[K+8>>3]=(+h[G+24>>3]- +h[G>>3]*+h[I+8>>3]- +h[G+8>>3]*+h[J+8>>3])/+h[G+16>>3];h[L>>3]=-+h[K>>3]*+h[K>>3];h[L+8>>3]=+h[K>>3]*-2.0*+h[K+8>>3];h[L+16>>3]=-+h[K+8>>3]*+h[K+8>>3];h[L>>3]=+h[L>>3]+ +h[I>>3]*+h[I>>3];eb=L+8|0;h[eb>>3]=+h[eb>>3]+ +h[I>>3]*2.0*(+h[I+8>>3]- +(c[(c[p>>2]|0)+12>>2]|0));eb=L+16|0;h[eb>>3]=+h[eb>>3]+(+h[I+8>>3]- +(c[(c[p>>2]|0)+12>>2]|0))*(+h[I+8>>3]- +(c[(c[p>>2]|0)+12>>2]|0));h[L>>3]=+h[L>>3]+ +h[J>>3]*+h[J>>3];eb=L+8|0;h[eb>>3]=+h[eb>>3]+ +h[J>>3]*2.0*(+h[J+8>>3]- +(c[(c[p>>2]|0)+16>>2]|0));eb=L+16|0;h[eb>>3]=+h[eb>>3]+(+h[J+8>>3]- +(c[(c[p>>2]|0)+16>>2]|0))*(+h[J+8>>3]- +(c[(c[p>>2]|0)+16>>2]|0));h[O>>3]=+h[L+8>>3]*+h[L+8>>3]- +h[L>>3]*4.0*+h[L+16>>3];if(!(+h[O>>3]>=0.0)){break}h[O>>3]=+N(+(+h[O>>3]));h[V>>3]=(-+h[L+8>>3]+ +h[O>>3])/(+h[L>>3]*2.0);h[t+(c[v>>2]<<3)>>3]=+h[I>>3]*+h[V>>3]+ +h[I+8>>3];h[u+(c[v>>2]<<3)>>3]=+h[J>>3]*+h[V>>3]+ +h[J+8>>3];c[v>>2]=(c[v>>2]|0)+1;h[V>>3]=(-+h[L+8>>3]- +h[O>>3])/(+h[L>>3]*2.0);h[t+(c[v>>2]<<3)>>3]=+h[I>>3]*+h[V>>3]+ +h[I+8>>3];h[u+(c[v>>2]<<3)>>3]=+h[J>>3]*+h[V>>3]+ +h[J+8>>3];c[v>>2]=(c[v>>2]|0)+1;break}if((c[q>>2]|0)==1){c[ba>>2]=c[(c[p>>2]|0)+12>>2];c[ca>>2]=c[(c[p+4>>2]|0)+12>>2];c[da>>2]=c[(c[p>>2]|0)+16>>2];c[ea>>2]=c[(c[p+4>>2]|0)+16>>2];c[fa>>2]=(c[ca>>2]|0)-(c[ba>>2]|0);c[ga>>2]=(c[ea>>2]|0)-(c[da>>2]|0);h[ha>>3]=+N(+(+(c[fa>>2]|0)*+(c[fa>>2]|0)+ +(c[ga>>2]|0)*+(c[ga>>2]|0)));h[W+8>>3]=+((c[ba>>2]|0)+(c[ca>>2]|0)|0)/2.0;h[X+8>>3]=+((c[da>>2]|0)+(c[ea>>2]|0)|0)/2.0;h[W>>3]=+(0-(c[ga>>2]|0)|0)/+h[ha>>3];h[X>>3]=+(c[fa>>2]|0)/+h[ha>>3];h[aa>>3]=+h[ha>>3]*.5;c[ia>>2]=c[(c[n>>2]|0)+12>>2];c[ja>>2]=c[(c[o>>2]|0)+12>>2];c[ka>>2]=c[(c[n>>2]|0)+16>>2];c[la>>2]=c[(c[o>>2]|0)+16>>2];c[ma>>2]=(c[ja>>2]|0)-(c[ia>>2]|0);c[na>>2]=(c[la>>2]|0)-(c[ka>>2]|0);h[oa>>3]=+N(+(+(c[ma>>2]|0)*+(c[ma>>2]|0)+ +(c[na>>2]|0)*+(c[na>>2]|0)));h[Y>>3]=(+h[W>>3]*+(c[na>>2]|0)- +h[X>>3]*+(c[ma>>2]|0))/+h[oa>>3];h[Y+8>>3]=((+h[W+8>>3]- +(c[ia>>2]|0))*+(c[na>>2]|0)-(+h[X+8>>3]- +(c[ka>>2]|0))*+(c[ma>>2]|0))/+h[oa>>3];h[_>>3]=+h[Y>>3]*+h[Y>>3];h[_+8>>3]=+h[Y>>3]*2.0*+h[Y+8>>3];h[_+16>>3]=+h[Y+8>>3]*+h[Y+8>>3];h[_>>3]=+h[_>>3]-1.0;eb=_+16|0;h[eb>>3]=+h[eb>>3]- +h[aa>>3]*+h[aa>>3];h[$>>3]=+h[_+8>>3]*+h[_+8>>3]- +h[_>>3]*4.0*+h[_+16>>3];if(!(+h[$>>3]>=0.0)){break}h[$>>3]=+N(+(+h[$>>3]));h[pa>>3]=(-+h[_+8>>3]+ +h[$>>3])/(+h[_>>3]*2.0);h[t+(c[v>>2]<<3)>>3]=+h[W>>3]*+h[pa>>3]+ +h[W+8>>3];h[u+(c[v>>2]<<3)>>3]=+h[X>>3]*+h[pa>>3]+ +h[X+8>>3];c[v>>2]=(c[v>>2]|0)+1;h[pa>>3]=(-+h[_+8>>3]- +h[$>>3])/(+h[_>>3]*2.0);h[t+(c[v>>2]<<3)>>3]=+h[W>>3]*+h[pa>>3]+ +h[W+8>>3];h[u+(c[v>>2]<<3)>>3]=+h[X>>3]*+h[pa>>3]+ +h[X+8>>3];c[v>>2]=(c[v>>2]|0)+1;break}if((c[q>>2]|0)==0){c[ta>>2]=0;while(1){if((c[ta>>2]|0)>=2){break}c[ua>>2]=c[(c[p+(c[ta>>2]<<2)>>2]|0)+12>>2];c[va>>2]=c[(c[p+((c[ta>>2]|0)+1<<2)>>2]|0)+12>>2];c[wa>>2]=c[(c[p+(c[ta>>2]<<2)>>2]|0)+16>>2];c[xa>>2]=c[(c[p+((c[ta>>2]|0)+1<<2)>>2]|0)+16>>2];c[ya>>2]=(c[va>>2]|0)-(c[ua>>2]|0);c[za>>2]=(c[xa>>2]|0)-(c[wa>>2]|0);h[qa+((c[ta>>2]<<1)+0<<3)>>3]=+(c[ya>>2]<<1|0);h[qa+((c[ta>>2]<<1)+1<<3)>>3]=+(c[za>>2]<<1|0);h[ra+(c[ta>>2]<<3)>>3]=+(c[ya>>2]|0)*+(c[ya>>2]|0)+ +(c[za>>2]|0)*+(c[za>>2]|0)+ +(c[ua>>2]|0)*2.0*+(c[ya>>2]|0)+ +(c[wa>>2]|0)*2.0*+(c[za>>2]|0);c[ta>>2]=(c[ta>>2]|0)+1}if((Ic(qa,ra,sa)|0)!=0){h[t+(c[v>>2]<<3)>>3]=+h[sa>>3];h[u+(c[v>>2]<<3)>>3]=+h[sa+8>>3];c[v>>2]=(c[v>>2]|0)+1}}}}while(0);c[m>>2]=0;while(1){if((c[m>>2]|0)>=(c[v>>2]|0)){break}h[Aa>>3]=+h[t+(c[m>>2]<<3)>>3];h[Ba>>3]=+h[u+(c[m>>2]<<3)>>3];c[Ea>>2]=0;c[Da>>2]=0;while(1){if((c[Da>>2]|0)>=(c[c[d>>2]>>2]|0)){break}c[Fa>>2]=c[(c[c[(c[(c[d>>2]|0)+4>>2]|0)+(c[Da>>2]<<2)>>2]>>2]|0)+12>>2];c[Ga>>2]=c[(c[(c[(c[(c[d>>2]|0)+4>>2]|0)+(c[Da>>2]<<2)>>2]|0)+4>>2]|0)+12>>2];c[Ha>>2]=c[(c[c[(c[(c[d>>2]|0)+4>>2]|0)+(c[Da>>2]<<2)>>2]>>2]|0)+16>>2];c[Ia>>2]=c[(c[(c[(c[(c[d>>2]|0)+4>>2]|0)+(c[Da>>2]<<2)>>2]|0)+4>>2]|0)+16>>2];if(+h[Ba>>3]>=+(c[Ha>>2]|0)?+h[Ba>>3]<+(c[Ia>>2]|0):0){hb=49}else{hb=47}if(((hb|0)==47?(hb=0,+h[Ba>>3]>=+(c[Ia>>2]|0)):0)?+h[Ba>>3]<+(c[Ha>>2]|0):0){hb=49}if((hb|0)==49){hb=0;c[Ja>>2]=(c[Ga>>2]|0)-(c[Fa>>2]|0);c[Ka>>2]=(c[Ia>>2]|0)-(c[Ha>>2]|0);if((c[Ka>>2]|0)<0){c[Ja>>2]=0-(c[Ja>>2]|0);c[Ka>>2]=0-(c[Ka>>2]|0)}if((+h[Aa>>3]- +(c[Fa>>2]|0))*+(c[Ka>>2]|0)>=(+h[Ba>>3]- +(c[Ha>>2]|0))*+(c[Ja>>2]|0)){c[Ea>>2]=c[Ea>>2]^1}}c[Da>>2]=(c[Da>>2]|0)+1}if((c[Ea>>2]|0)!=0){h[La>>3]=r;c[Na>>2]=0;while(1){if((c[Na>>2]|0)>=(c[c[d>>2]>>2]|0)){break}c[Oa>>2]=c[(c[(c[(c[d>>2]|0)+8>>2]|0)+(c[Na>>2]<<2)>>2]|0)+12>>2];c[Pa>>2]=c[(c[(c[(c[d>>2]|0)+8>>2]|0)+(c[Na>>2]<<2)>>2]|0)+16>>2];h[Qa>>3]=+h[Aa>>3]- +(c[Oa>>2]|0);h[Ra>>3]=+h[Ba>>3]- +(c[Pa>>2]|0);h[Sa>>3]=+h[Qa>>3]*+h[Qa>>3]+ +h[Ra>>3]*+h[Ra>>3];if(+h[La>>3]>+h[Sa>>3]){h[La>>3]=+h[Sa>>3]}c[Na>>2]=(c[Na>>2]|0)+1}c[Ma>>2]=0;while(1){if((c[Ma>>2]|0)>=(c[c[d>>2]>>2]|0)){break}c[Ta>>2]=c[(c[c[(c[(c[d>>2]|0)+4>>2]|0)+(c[Ma>>2]<<2)>>2]>>2]|0)+12>>2];c[Ua>>2]=c[(c[(c[(c[(c[d>>2]|0)+4>>2]|0)+(c[Ma>>2]<<2)>>2]|0)+4>>2]|0)+12>>2];c[Va>>2]=c[(c[c[(c[(c[d>>2]|0)+4>>2]|0)+(c[Ma>>2]<<2)>>2]>>2]|0)+16>>2];c[Wa>>2]=c[(c[(c[(c[(c[d>>2]|0)+4>>2]|0)+(c[Ma>>2]<<2)>>2]|0)+4>>2]|0)+16>>2];c[Xa>>2]=(c[Ua>>2]|0)-(c[Ta>>2]|0);c[Ya>>2]=(c[Wa>>2]|0)-(c[Va>>2]|0);h[Za>>3]=+h[Aa>>3]- +(c[Ta>>2]|0);h[_a>>3]=+h[Ba>>3]- +(c[Va>>2]|0);h[$a>>3]=+h[Za>>3]*+(c[Xa>>2]|0)+ +h[_a>>3]*+(c[Ya>>2]|0);eb=Z(c[Xa>>2]|0,c[Xa>>2]|0)|0;c[ab>>2]=eb+(Z(c[Ya>>2]|0,c[Ya>>2]|0)|0);if((0.0<+h[$a>>3]?+h[$a>>3]<+(c[ab>>2]|0):0)?(h[bb>>3]=+h[Za>>3]*+(c[Ya>>2]|0)- +h[_a>>3]*+(c[Xa>>2]|0),h[cb>>3]=+h[bb>>3]*+h[bb>>3]/+(c[ab>>2]|0),+h[La>>3]>+h[cb>>3]):0){h[La>>3]=+h[cb>>3]}c[Ma>>2]=(c[Ma>>2]|0)+1}if(+h[g>>3]<+h[La>>3]){h[g>>3]=+h[La>>3];h[e>>3]=+h[Aa>>3];h[f>>3]=+h[Ba>>3]}}c[m>>2]=(c[m>>2]|0)+1}if((c[l>>2]|0)<(c[c[d>>2]>>2]|0)){c[q>>2]=(c[q>>2]|0)+ -1}else{c[s>>2]=(c[s>>2]|0)+ -1}c[l>>2]=(c[l>>2]|0)+1}if((c[k>>2]|0)<(c[c[d>>2]>>2]|0)){c[q>>2]=(c[q>>2]|0)+ -1}else{c[s>>2]=(c[s>>2]|0)+ -1}c[k>>2]=(c[k>>2]|0)+1}if((c[j>>2]|0)<(c[c[d>>2]>>2]|0)){c[q>>2]=(c[q>>2]|0)+ -1}else{c[s>>2]=(c[s>>2]|0)+ -1}c[j>>2]=(c[j>>2]|0)+1}if(!(+h[g>>3]>0.0)){Ca(272,248,1365,288)}c[(c[d>>2]|0)+12>>2]=1;c[(c[d>>2]|0)+16>>2]=~~(+h[e>>3]+.5);c[(c[d>>2]|0)+20>>2]=~~(+h[f>>3]+.5);i=b;return}function Hc(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,j=0,k=0,l=0,m=0,n=0;e=i;i=i+96|0;f=e+92|0;g=e+88|0;j=e+84|0;k=e+80|0;l=e+8|0;m=e;c[g>>2]=a;c[j>>2]=b;c[k>>2]=d;h[m>>3]=+h[c[g>>2]>>3]*+h[(c[g>>2]|0)+32>>3]*+h[(c[g>>2]|0)+64>>3]+ +h[(c[g>>2]|0)+8>>3]*+h[(c[g>>2]|0)+40>>3]*+h[(c[g>>2]|0)+48>>3]+ +h[(c[g>>2]|0)+16>>3]*+h[(c[g>>2]|0)+24>>3]*+h[(c[g>>2]|0)+56>>3]- +h[c[g>>2]>>3]*+h[(c[g>>2]|0)+40>>3]*+h[(c[g>>2]|0)+56>>3]- +h[(c[g>>2]|0)+8>>3]*+h[(c[g>>2]|0)+24>>3]*+h[(c[g>>2]|0)+64>>3]- +h[(c[g>>2]|0)+16>>3]*+h[(c[g>>2]|0)+32>>3]*+h[(c[g>>2]|0)+48>>3];if(+h[m>>3]==0.0){c[f>>2]=0;n=c[f>>2]|0;i=e;return n|0}else{h[l>>3]=(+h[(c[g>>2]|0)+32>>3]*+h[(c[g>>2]|0)+64>>3]- +h[(c[g>>2]|0)+40>>3]*+h[(c[g>>2]|0)+56>>3])/+h[m>>3];h[l+8>>3]=(+h[(c[g>>2]|0)+16>>3]*+h[(c[g>>2]|0)+56>>3]- +h[(c[g>>2]|0)+8>>3]*+h[(c[g>>2]|0)+64>>3])/+h[m>>3];h[l+16>>3]=(+h[(c[g>>2]|0)+8>>3]*+h[(c[g>>2]|0)+40>>3]- +h[(c[g>>2]|0)+16>>3]*+h[(c[g>>2]|0)+32>>3])/+h[m>>3];h[l+24>>3]=(+h[(c[g>>2]|0)+40>>3]*+h[(c[g>>2]|0)+48>>3]- +h[(c[g>>2]|0)+24>>3]*+h[(c[g>>2]|0)+64>>3])/+h[m>>3];h[l+32>>3]=(+h[c[g>>2]>>3]*+h[(c[g>>2]|0)+64>>3]- +h[(c[g>>2]|0)+16>>3]*+h[(c[g>>2]|0)+48>>3])/+h[m>>3];h[l+40>>3]=(+h[(c[g>>2]|0)+16>>3]*+h[(c[g>>2]|0)+24>>3]- +h[c[g>>2]>>3]*+h[(c[g>>2]|0)+40>>3])/+h[m>>3];h[l+48>>3]=(+h[(c[g>>2]|0)+24>>3]*+h[(c[g>>2]|0)+56>>3]- +h[(c[g>>2]|0)+32>>3]*+h[(c[g>>2]|0)+48>>3])/+h[m>>3];h[l+56>>3]=(+h[(c[g>>2]|0)+8>>3]*+h[(c[g>>2]|0)+48>>3]- +h[c[g>>2]>>3]*+h[(c[g>>2]|0)+56>>3])/+h[m>>3];h[l+64>>3]=(+h[c[g>>2]>>3]*+h[(c[g>>2]|0)+32>>3]- +h[(c[g>>2]|0)+8>>3]*+h[(c[g>>2]|0)+24>>3])/+h[m>>3];h[c[k>>2]>>3]=+h[l>>3]*+h[c[j>>2]>>3]+ +h[l+8>>3]*+h[(c[j>>2]|0)+8>>3]+ +h[l+16>>3]*+h[(c[j>>2]|0)+16>>3];h[(c[k>>2]|0)+8>>3]=+h[l+24>>3]*+h[c[j>>2]>>3]+ +h[l+32>>3]*+h[(c[j>>2]|0)+8>>3]+ +h[l+40>>3]*+h[(c[j>>2]|0)+16>>3];h[(c[k>>2]|0)+16>>3]=+h[l+48>>3]*+h[c[j>>2]>>3]+ +h[l+56>>3]*+h[(c[j>>2]|0)+8>>3]+ +h[l+64>>3]*+h[(c[j>>2]|0)+16>>3];c[f>>2]=1;n=c[f>>2]|0;i=e;return n|0}return 0}function Ic(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,j=0,k=0,l=0,m=0,n=0;e=i;i=i+64|0;f=e+52|0;g=e+48|0;j=e+44|0;k=e+40|0;l=e+8|0;m=e;c[g>>2]=a;c[j>>2]=b;c[k>>2]=d;h[m>>3]=+h[c[g>>2]>>3]*+h[(c[g>>2]|0)+24>>3]- +h[(c[g>>2]|0)+8>>3]*+h[(c[g>>2]|0)+16>>3];if(+h[m>>3]==0.0){c[f>>2]=0;n=c[f>>2]|0;i=e;return n|0}else{h[l>>3]=+h[(c[g>>2]|0)+24>>3]/+h[m>>3];h[l+8>>3]=-+h[(c[g>>2]|0)+8>>3]/+h[m>>3];h[l+16>>3]=-+h[(c[g>>2]|0)+16>>3]/+h[m>>3];h[l+24>>3]=+h[c[g>>2]>>3]/+h[m>>3];h[c[k>>2]>>3]=+h[l>>3]*+h[c[j>>2]>>3]+ +h[l+8>>3]*+h[(c[j>>2]|0)+8>>3];h[(c[k>>2]|0)+8>>3]=+h[l+16>>3]*+h[c[j>>2]>>3]+ +h[l+24>>3]*+h[(c[j>>2]|0)+8>>3];c[f>>2]=1;n=c[f>>2]|0;i=e;return n|0}return 0}function Jc(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0;f=i;i=i+32|0;g=f+16|0;h=f+12|0;j=f+8|0;k=f+4|0;l=f;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;e=c[h>>2]|0;if((c[h>>2]|0)==11|(c[h>>2]|0)==12){c[g>>2]=Kc(e,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0)|0;m=c[g>>2]|0;i=f;return m|0}if((e|0)==2){c[g>>2]=bg(312)|0;m=c[g>>2]|0;i=f;return m|0}else{c[g>>2]=0;m=c[g>>2]|0;i=f;return m|0}return 0}function Kc(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0.0;f=i;i=i+336|0;g=f+8|0;j=f+68|0;k=f+64|0;l=f+60|0;m=f+56|0;n=f+52|0;o=f+48|0;p=f+44|0;q=f+40|0;r=f+36|0;s=f+32|0;t=f;u=f+28|0;v=f+72|0;w=f+24|0;x=f+20|0;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=100;c[w>>2]=(c[j>>2]|0)==11?0:1;do{Wg(c[w>>2]|0,c[n>>2]|0,c[k>>2]|0,c[l>>2]|0,t,o,p);j=Z(c[k>>2]|0,c[k>>2]|0)|0;c[u>>2]=~~(+h[t>>3]- +N(+(+(j+(Z(c[l>>2]|0,c[l>>2]|0)|0)|0))));do{j=jh(c[m>>2]|0,c[u>>2]<<1)|0;c[q>>2]=j-(c[u>>2]|0);j=jh(c[m>>2]|0,c[u>>2]<<1)|0;c[r>>2]=j-(c[u>>2]|0);j=Z(c[q>>2]|0,c[q>>2]|0)|0;y=+N(+(+(j+(Z(c[r>>2]|0,c[r>>2]|0)|0)|0)))}while(y>+(c[u>>2]|0));c[s>>2]=(jh(c[m>>2]|0,10)|0)*36;j=c[r>>2]|0;e=c[s>>2]|0;c[g>>2]=c[q>>2];c[g+4>>2]=j;c[g+8>>2]=e;cb(v|0,536,g|0)|0;c[x>>2]=pd(c[k>>2]|0,c[l>>2]|0,c[w>>2]|0,v)|0}while((c[x>>2]|0)==0);Dc(c[x>>2]|0);x=bg(v)|0;i=f;return x|0}function Lc(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0;f=i;i=i+32|0;g=f+16|0;h=f+12|0;j=f+8|0;k=f+4|0;l=f;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;e=c[h>>2]|0;do{if(!((c[h>>2]|0)==11|(c[h>>2]|0)==12)){if((e|0)==2){c[g>>2]=Nc(c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0)|0;break}if((c[l>>2]|0)!=0){c[g>>2]=320;break}else{c[g>>2]=0;break}}else{c[g>>2]=Mc(e,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0)|0}}while(0);i=f;return c[g>>2]|0}function Mc(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0.0;f=i;i=i+80|0;g=f+8|0;j=f+72|0;k=f+68|0;l=f+64|0;m=f+60|0;n=f+56|0;o=f+52|0;p=f+40|0;q=f+36|0;r=f+32|0;s=f+28|0;t=f;u=f+24|0;v=f+20|0;c[k>>2]=a;c[l>>2]=b;c[m>>2]=d;c[n>>2]=e;c[o>>2]=100;c[u>>2]=(c[k>>2]|0)==11?0:1;if((c[n>>2]|0)==0){c[j>>2]=1152;w=c[j>>2]|0;i=f;return w|0}Wg(c[u>>2]|0,c[o>>2]|0,c[l>>2]|0,c[m>>2]|0,t,f+48|0,f+44|0);o=Z(c[l>>2]|0,c[l>>2]|0)|0;c[s>>2]=~~(+h[t>>3]- +N(+(+(o+(Z(c[m>>2]|0,c[m>>2]|0)|0)|0))));o=c[n>>2]|0;c[g>>2]=p;c[g+4>>2]=q;c[g+8>>2]=r;if((Ka(o|0,536,g|0)|0)!=3){c[j>>2]=1192;w=c[j>>2]|0;i=f;return w|0}g=Z(c[p>>2]|0,c[p>>2]|0)|0;x=+N(+(+(g+(Z(c[q>>2]|0,c[q>>2]|0)|0)|0)));if(x>+(c[s>>2]|0)){c[j>>2]=1232;w=c[j>>2]|0;i=f;return w|0}if(((c[r>>2]|0)%36|0|0)!=0|(c[r>>2]|0)<0|(c[r>>2]|0)>=360){c[j>>2]=1264;w=c[j>>2]|0;i=f;return w|0}c[v>>2]=pd(c[l>>2]|0,c[m>>2]|0,c[u>>2]|0,c[n>>2]|0)|0;if((c[v>>2]|0)!=0){Dc(c[v>>2]|0);c[j>>2]=0;w=c[j>>2]|0;i=f;return w|0}else{c[j>>2]=1296;w=c[j>>2]|0;i=f;return w|0}return 0}function Nc(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0;f=i;i=i+32|0;g=f+16|0;h=f;c[f+12>>2]=a;c[f+8>>2]=b;c[f+4>>2]=d;c[h>>2]=e;if((c[h>>2]|0)!=0?(Lh(c[h>>2]|0,312)|0)!=0:0){c[g>>2]=1120;j=c[g>>2]|0;i=f;return j|0}c[g>>2]=0;j=c[g>>2]|0;i=f;return j|0}function Oc(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0;f=i;i=i+32|0;g=f+16|0;h=f+12|0;j=f+8|0;k=f+4|0;l=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=Lc(c[g>>2]|0,c[h>>2]|0,c[j>>2]|0,c[k>>2]|0)|0;if((c[l>>2]|0)!=0){Ca(376,248,2883,408)}else{l=Mb[c[424+(c[g>>2]<<2)>>2]&31](c[h>>2]|0,c[j>>2]|0,c[k>>2]|0)|0;i=f;return l|0}return 0}function Pc(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0;h=i;i=i+32|0;j=h+20|0;k=h+16|0;l=h+12|0;m=h+8|0;n=h+4|0;o=h;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=f;c[o>>2]=g;Eb[c[480+(c[j>>2]<<2)>>2]&31](c[k>>2]|0,c[l>>2]|0,c[m>>2]|0,c[n>>2]|0,c[o>>2]|0);i=h;return}function Qc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0;g=i;i=i+32|0;h=g+20|0;j=g+16|0;k=g+12|0;l=g+8|0;m=g+4|0;n=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=20;c[c[k>>2]>>2]=c[n>>2];k=Z(c[h>>2]|0,c[n>>2]|0)|0;c[c[l>>2]>>2]=k;k=Z(c[j>>2]|0,c[n>>2]|0)|0;c[c[m>>2]>>2]=k;i=g;return}function Rc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;g=i;i=i+32|0;h=g+24|0;j=g+20|0;k=g+16|0;l=g+12|0;m=g+8|0;n=g+4|0;o=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=15;c[o>>2]=26;c[c[k>>2]>>2]=45;k=Z((c[n>>2]|0)*3|0,(c[h>>2]|0)-1|0)|0;c[c[l>>2]>>2]=k+(c[n>>2]<<2);n=Z(c[o>>2]<<1,(c[j>>2]|0)-1|0)|0;c[c[m>>2]>>2]=n+((c[o>>2]|0)*3|0);i=g;return}function Sc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;g=i;i=i+32|0;h=g+24|0;j=g+20|0;k=g+16|0;l=g+12|0;m=g+8|0;n=g+4|0;o=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=15;c[o>>2]=26;c[c[k>>2]>>2]=18;k=Z((c[h>>2]|0)+1<<1,c[n>>2]|0)|0;c[c[l>>2]>>2]=k;k=Z(c[j>>2]|0,c[o>>2]|0)|0;c[c[m>>2]>>2]=k;i=g;return}function Tc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;g=i;i=i+32|0;h=g+24|0;j=g+20|0;k=g+16|0;l=g+12|0;m=g+8|0;n=g+4|0;o=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=15;c[o>>2]=26;c[c[k>>2]>>2]=18;k=Z((c[n>>2]|0)+(c[o>>2]|0)|0,(c[h>>2]|0)-1|0)|0;c[c[l>>2]>>2]=k+(c[n>>2]|0)+(c[o>>2]|0);k=Z((c[n>>2]|0)+(c[o>>2]|0)|0,(c[j>>2]|0)-1|0)|0;c[c[m>>2]>>2]=k+(c[n>>2]|0)+(c[o>>2]|0);i=g;return}function Uc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0;g=i;i=i+32|0;h=g+20|0;j=g+16|0;k=g+12|0;l=g+8|0;m=g+4|0;n=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=31;c[c[k>>2]>>2]=40;k=Z(c[n>>2]<<1,(c[h>>2]|0)-1|0)|0;c[c[l>>2]>>2]=k+(c[n>>2]<<1);k=Z(c[n>>2]<<1,(c[j>>2]|0)-1|0)|0;c[c[m>>2]>>2]=k+(c[n>>2]<<1);i=g;return}function Vc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;g=i;i=i+32|0;h=g+24|0;j=g+20|0;k=g+16|0;l=g+12|0;m=g+8|0;n=g+4|0;o=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=15;c[o>>2]=26;c[c[k>>2]>>2]=18;k=Z(((c[n>>2]|0)*3|0)+(c[o>>2]|0)|0,(c[h>>2]|0)-1|0)|0;c[c[l>>2]>>2]=k+(c[n>>2]<<2);k=Z((c[n>>2]<<1)+(c[o>>2]<<1)|0,(c[j>>2]|0)-1|0)|0;c[c[m>>2]>>2]=k+((c[o>>2]|0)*3|0)+(c[n>>2]|0);i=g;return}function Wc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;g=i;i=i+32|0;h=g+24|0;j=g+20|0;k=g+16|0;l=g+12|0;m=g+8|0;n=g+4|0;o=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=29;c[o>>2]=41;c[c[k>>2]>>2]=40;k=Z((c[n>>2]<<1)+(c[o>>2]|0)|0,c[h>>2]|0)|0;c[c[l>>2]>>2]=k;k=Z((c[n>>2]<<1)+(c[o>>2]|0)|0,c[j>>2]|0)|0;c[c[m>>2]>>2]=k;i=g;return}function Xc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;g=i;i=i+32|0;h=g+24|0;j=g+20|0;k=g+16|0;l=g+12|0;m=g+8|0;n=g+4|0;o=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=15;c[o>>2]=26;c[c[k>>2]>>2]=40;k=Z(c[o>>2]<<2,c[h>>2]|0)|0;c[c[l>>2]>>2]=k+(c[o>>2]<<1);o=Z((c[n>>2]|0)*6|0,(c[j>>2]|0)-1|0)|0;c[c[m>>2]>>2]=o+(c[n>>2]<<3);i=g;return}function Yc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;g=i;i=i+48|0;h=g+36|0;j=g+32|0;k=g+28|0;l=g+24|0;m=g+20|0;n=g+16|0;o=g+12|0;p=g+8|0;q=g+4|0;r=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=75;c[o>>2]=-26;c[p>>2]=(c[n>>2]<<2|0)/5|0;c[q>>2]=0-(c[o>>2]|0)<<1;c[r>>2]=(c[q>>2]|0)-(c[o>>2]|0);c[c[k>>2]>>2]=150;k=Z((((c[n>>2]|0)*6|0)+((c[p>>2]|0)*3|0)|0)/2|0,(c[h>>2]|0)-1|0)|0;c[c[l>>2]>>2]=k+(c[p>>2]<<2)+(c[n>>2]<<1);n=Z(((c[q>>2]|0)*5|0)-(c[o>>2]<<2)|0,(c[j>>2]|0)-1|0)|0;c[c[m>>2]>>2]=n+(c[q>>2]<<2)+(c[r>>2]<<1);i=g;return}function Zc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;g=i;i=i+32|0;h=g+24|0;j=g+20|0;k=g+16|0;l=g+12|0;m=g+8|0;n=g+4|0;o=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=15;c[o>>2]=26;c[c[k>>2]>>2]=26;k=Z((c[n>>2]<<2)+(c[o>>2]<<1)|0,(c[h>>2]|0)-1|0)|0;c[c[l>>2]>>2]=k+(((c[n>>2]<<1)+(c[o>>2]|0)|0)*3|0);k=Z(((c[n>>2]|0)*3|0)+(c[o>>2]<<1)|0,(c[j>>2]|0)-1|0)|0;c[c[m>>2]>>2]=k+((c[n>>2]<<1)+(c[o>>2]|0)<<1);i=g;return}function _c(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;g=i;i=i+32|0;h=g+24|0;j=g+20|0;k=g+16|0;l=g+12|0;m=g+8|0;n=g+4|0;o=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=15;c[o>>2]=26;c[c[k>>2]>>2]=26;k=Z(((c[n>>2]|0)*6|0)+(c[o>>2]<<1)|0,(c[h>>2]|0)-1|0)|0;c[c[l>>2]>>2]=k+((c[n>>2]<<1)+(c[o>>2]|0)<<1)+((c[n>>2]|0)*3|0)+(c[o>>2]|0);k=Z(((c[n>>2]|0)*3|0)+((c[o>>2]|0)*3|0)|0,(c[j>>2]|0)-1|0)|0;c[c[m>>2]>>2]=k+((c[n>>2]<<1)+(c[o>>2]|0)<<1);i=g;return}function $c(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0;g=i;i=i+32|0;h=g+16|0;j=g+12|0;k=g+8|0;l=g+4|0;m=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;bd(c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0);i=g;return}function ad(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0;g=i;i=i+32|0;h=g+16|0;j=g+12|0;k=g+8|0;l=g+4|0;m=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;bd(c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0);i=g;return}function bd(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0;g=i;i=i+32|0;h=g+20|0;j=g+16|0;k=g+12|0;l=g+8|0;m=g+4|0;n=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=100;c[c[k>>2]>>2]=c[n>>2];k=Z(c[n>>2]|0,c[h>>2]|0)|0;c[c[l>>2]>>2]=k;k=Z(c[n>>2]|0,c[j>>2]|0)|0;c[c[m>>2]>>2]=k;i=g;return}function cd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;e=i;i=i+64|0;f=e+48|0;g=e+44|0;h=e+36|0;j=e+32|0;k=e+28|0;l=e+24|0;m=e+20|0;n=e+16|0;o=e+12|0;p=e+8|0;q=e+4|0;r=e;c[f>>2]=a;c[g>>2]=b;c[e+40>>2]=d;c[k>>2]=20;c[l>>2]=Z(c[f>>2]|0,c[g>>2]|0)|0;c[m>>2]=Z((c[f>>2]|0)+1|0,(c[g>>2]|0)+1|0)|0;c[o>>2]=rd()|0;c[(c[o>>2]|0)+40>>2]=c[k>>2];d=_f((c[l>>2]|0)*24|0)|0;c[(c[o>>2]|0)+4>>2]=d;d=_f((c[m>>2]|0)*20|0)|0;c[(c[o>>2]|0)+20>>2]=d;c[n>>2]=lh(8)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[g>>2]|0)){break}c[h>>2]=0;while(1){if((c[h>>2]|0)>=(c[f>>2]|0)){break}c[q>>2]=Z(c[k>>2]|0,c[h>>2]|0)|0;c[r>>2]=Z(c[k>>2]|0,c[j>>2]|0)|0;zd(c[o>>2]|0,4);c[p>>2]=Ad(c[o>>2]|0,c[n>>2]|0,c[q>>2]|0,c[r>>2]|0)|0;Bd(c[o>>2]|0,c[p>>2]|0,0);c[p>>2]=Ad(c[o>>2]|0,c[n>>2]|0,(c[q>>2]|0)+(c[k>>2]|0)|0,c[r>>2]|0)|0;Bd(c[o>>2]|0,c[p>>2]|0,1);c[p>>2]=Ad(c[o>>2]|0,c[n>>2]|0,(c[q>>2]|0)+(c[k>>2]|0)|0,(c[r>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[o>>2]|0,c[p>>2]|0,2);c[p>>2]=Ad(c[o>>2]|0,c[n>>2]|0,c[q>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[o>>2]|0,c[p>>2]|0,3);c[h>>2]=(c[h>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+1}mh(c[n>>2]|0);if((c[c[o>>2]>>2]|0)>(c[l>>2]|0)){Ca(576,248,1440,1104)}if((c[(c[o>>2]|0)+16>>2]|0)<=(c[m>>2]|0)){ud(c[o>>2]|0);i=e;return c[o>>2]|0}else{Ca(608,248,1441,1104)}return 0}function dd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;e=i;i=i+64|0;f=e+52|0;g=e+48|0;h=e+40|0;j=e+36|0;k=e+32|0;l=e+28|0;m=e+24|0;n=e+20|0;o=e+16|0;p=e+12|0;q=e+8|0;r=e+4|0;s=e;c[f>>2]=a;c[g>>2]=b;c[e+44>>2]=d;c[k>>2]=15;c[l>>2]=26;c[m>>2]=Z(c[f>>2]|0,c[g>>2]|0)|0;c[n>>2]=Z((c[f>>2]|0)+1<<1,(c[g>>2]|0)+1|0)|0;c[p>>2]=rd()|0;c[(c[p>>2]|0)+40>>2]=45;d=_f((c[m>>2]|0)*24|0)|0;c[(c[p>>2]|0)+4>>2]=d;d=_f((c[n>>2]|0)*20|0)|0;c[(c[p>>2]|0)+20>>2]=d;c[o>>2]=lh(8)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[g>>2]|0)){break}c[h>>2]=0;while(1){if((c[h>>2]|0)>=(c[f>>2]|0)){break}c[r>>2]=Z((c[k>>2]|0)*3|0,c[h>>2]|0)|0;c[s>>2]=Z(c[l>>2]<<1,c[j>>2]|0)|0;if(((c[h>>2]|0)%2|0|0)!=0){c[s>>2]=(c[s>>2]|0)+(c[l>>2]|0)}zd(c[p>>2]|0,6);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)-(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)-(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]<<1)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]<<1)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,5);c[h>>2]=(c[h>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+1}mh(c[o>>2]|0);if((c[c[p>>2]>>2]|0)>(c[m>>2]|0)){Ca(576,248,1509,1080)}if((c[(c[p>>2]|0)+16>>2]|0)<=(c[n>>2]|0)){ud(c[p>>2]|0);i=e;return c[p>>2]|0}else{Ca(608,248,1510,1080)}return 0}function ed(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0;e=i;i=i+112|0;f=e+104|0;g=e+100|0;h=e+96|0;j=e+92|0;k=e+88|0;l=e+84|0;m=e+80|0;n=e+76|0;o=e+72|0;p=e+68|0;q=e+64|0;r=e+60|0;s=e+56|0;t=e+52|0;u=e+48|0;v=e+44|0;w=e+40|0;x=e+36|0;y=e+32|0;z=e+28|0;A=e+24|0;B=e+20|0;C=e+16|0;D=e+12|0;E=e+8|0;F=e+4|0;G=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;if((c[h>>2]|0)==0){H=-1}else{H=Kh(c[h>>2]|0)|0}c[l>>2]=H;c[m>>2]=15;c[n>>2]=26;c[p>>2]=(c[f>>2]|0)+1;c[q>>2]=rd()|0;c[(c[q>>2]|0)+40>>2]=18;if((c[l>>2]|0)==-1){l=(Z(c[f>>2]|0,c[g>>2]|0)|0)<<1;c[c[q>>2]>>2]=l;l=Z((c[f>>2]|0)+1|0,(c[g>>2]|0)+1|0)|0;c[(c[q>>2]|0)+16>>2]=l;l=_f((c[c[q>>2]>>2]|0)*24|0)|0;c[(c[q>>2]|0)+4>>2]=l;l=_f((c[(c[q>>2]|0)+16>>2]|0)*20|0)|0;c[(c[q>>2]|0)+20>>2]=l;c[o>>2]=0;c[k>>2]=0;while(1){if((c[k>>2]|0)>(c[g>>2]|0)){break}c[j>>2]=0;while(1){if((c[j>>2]|0)>(c[f>>2]|0)){break}c[r>>2]=(c[(c[q>>2]|0)+20>>2]|0)+((c[o>>2]|0)*20|0);c[c[r>>2]>>2]=0;c[(c[r>>2]|0)+4>>2]=0;c[(c[r>>2]|0)+8>>2]=0;l=Z(c[j>>2]<<1,c[m>>2]|0)|0;c[(c[r>>2]|0)+12>>2]=l+(((c[k>>2]|0)%2|0|0)!=0?c[m>>2]|0:0);l=Z(c[k>>2]|0,c[n>>2]|0)|0;c[(c[r>>2]|0)+16>>2]=l;c[o>>2]=(c[o>>2]|0)+1;c[j>>2]=(c[j>>2]|0)+1}c[k>>2]=(c[k>>2]|0)+1}c[o>>2]=0;c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[g>>2]|0)){break}c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[f>>2]|0)){break}c[s>>2]=(c[(c[q>>2]|0)+4>>2]|0)+((c[o>>2]|0)*24|0);c[t>>2]=(c[s>>2]|0)+24;c[(c[s>>2]|0)+4>>2]=0;c[c[s>>2]>>2]=3;r=_f(c[c[s>>2]>>2]<<2)|0;c[(c[s>>2]|0)+8>>2]=r;c[(c[s>>2]|0)+12>>2]=0;c[(c[t>>2]|0)+4>>2]=0;c[c[t>>2]>>2]=3;r=_f(c[c[t>>2]>>2]<<2)|0;c[(c[t>>2]|0)+8>>2]=r;c[(c[t>>2]|0)+12>>2]=0;r=((c[k>>2]|0)%2|0|0)!=0;l=(c[(c[q>>2]|0)+20>>2]|0)+((Z(c[k>>2]|0,c[p>>2]|0)|0)*20|0)|0;c[c[(c[s>>2]|0)+8>>2]>>2]=l+((c[j>>2]|0)*20|0);l=c[(c[q>>2]|0)+20>>2]|0;H=c[k>>2]|0;if(r){r=l+((Z(H+1|0,c[p>>2]|0)|0)*20|0)|0;c[(c[(c[s>>2]|0)+8>>2]|0)+4>>2]=r+((c[j>>2]|0)*20|0)+20;r=(c[(c[q>>2]|0)+20>>2]|0)+((Z((c[k>>2]|0)+1|0,c[p>>2]|0)|0)*20|0)|0;c[(c[(c[s>>2]|0)+8>>2]|0)+8>>2]=r+((c[j>>2]|0)*20|0);r=(c[(c[q>>2]|0)+20>>2]|0)+((Z(c[k>>2]|0,c[p>>2]|0)|0)*20|0)|0;c[c[(c[t>>2]|0)+8>>2]>>2]=r+((c[j>>2]|0)*20|0);r=(c[(c[q>>2]|0)+20>>2]|0)+((Z(c[k>>2]|0,c[p>>2]|0)|0)*20|0)|0;c[(c[(c[t>>2]|0)+8>>2]|0)+4>>2]=r+((c[j>>2]|0)*20|0)+20;r=(c[(c[q>>2]|0)+20>>2]|0)+((Z((c[k>>2]|0)+1|0,c[p>>2]|0)|0)*20|0)|0;c[(c[(c[t>>2]|0)+8>>2]|0)+8>>2]=r+((c[j>>2]|0)*20|0)+20}else{r=l+((Z(H,c[p>>2]|0)|0)*20|0)|0;c[(c[(c[s>>2]|0)+8>>2]|0)+4>>2]=r+((c[j>>2]|0)*20|0)+20;r=(c[(c[q>>2]|0)+20>>2]|0)+((Z((c[k>>2]|0)+1|0,c[p>>2]|0)|0)*20|0)|0;c[(c[(c[s>>2]|0)+8>>2]|0)+8>>2]=r+((c[j>>2]|0)*20|0);r=(c[(c[q>>2]|0)+20>>2]|0)+((Z(c[k>>2]|0,c[p>>2]|0)|0)*20|0)|0;c[c[(c[t>>2]|0)+8>>2]>>2]=r+((c[j>>2]|0)*20|0)+20;r=(c[(c[q>>2]|0)+20>>2]|0)+((Z((c[k>>2]|0)+1|0,c[p>>2]|0)|0)*20|0)|0;c[(c[(c[t>>2]|0)+8>>2]|0)+4>>2]=r+((c[j>>2]|0)*20|0)+20;r=(c[(c[q>>2]|0)+20>>2]|0)+((Z((c[k>>2]|0)+1|0,c[p>>2]|0)|0)*20|0)|0;c[(c[(c[t>>2]|0)+8>>2]|0)+8>>2]=r+((c[j>>2]|0)*20|0)}c[o>>2]=(c[o>>2]|0)+2;c[j>>2]=(c[j>>2]|0)+1}c[k>>2]=(c[k>>2]|0)+1}I=c[q>>2]|0;ud(I);J=c[q>>2]|0;i=e;return J|0}c[u>>2]=lh(8)|0;c[v>>2]=Z(c[g>>2]|0,(c[f>>2]<<1)+1|0)|0;c[w>>2]=(Z((c[g>>2]|0)+1|0,(c[f>>2]|0)+1|0)|0)<<2;o=_f((c[v>>2]|0)*24|0)|0;c[(c[q>>2]|0)+4>>2]=o;o=_f((c[w>>2]|0)*20|0)|0;c[(c[q>>2]|0)+20>>2]=o;c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[g>>2]|0)){break}o=Z(c[k>>2]|0,c[n>>2]|0)|0;c[y>>2]=o;c[x>>2]=o;o=c[n>>2]|0;if(((c[k>>2]|0)%2|0|0)!=0){c[y>>2]=(c[y>>2]|0)+o;c[z>>2]=2;c[A>>2]=1}else{c[x>>2]=(c[x>>2]|0)+o;c[z>>2]=1;c[A>>2]=2}c[j>>2]=0;while(1){if((c[j>>2]|0)>(c[f>>2]|0)){break}c[B>>2]=Z(c[j>>2]<<1,c[m>>2]|0)|0;c[C>>2]=(c[B>>2]|0)+(c[m>>2]|0);c[D>>2]=(c[C>>2]|0)+(c[m>>2]|0);if(((c[g>>2]|0)%2|0|0)==1?(c[k>>2]|0)==((c[g>>2]|0)-1|0):0){if((c[j>>2]|0)!=0?(c[j>>2]|0)!=(c[f>>2]|0):0){K=30}}else{K=30}if((K|0)==30){K=0;zd(c[q>>2]|0,3);o=c[q>>2]|0;Bd(o,Ad(c[q>>2]|0,c[u>>2]|0,c[B>>2]|0,c[x>>2]|0)|0,0);o=c[q>>2]|0;t=Ad(c[q>>2]|0,c[u>>2]|0,c[C>>2]|0,c[y>>2]|0)|0;Bd(o,t,c[z>>2]|0);t=c[q>>2]|0;o=Ad(c[q>>2]|0,c[u>>2]|0,c[D>>2]|0,c[x>>2]|0)|0;Bd(t,o,c[A>>2]|0)}c[j>>2]=(c[j>>2]|0)+1}c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[f>>2]|0)){break}c[E>>2]=Z((c[j>>2]<<1)+1|0,c[m>>2]|0)|0;c[F>>2]=(c[E>>2]|0)+(c[m>>2]|0);c[G>>2]=(c[F>>2]|0)+(c[m>>2]|0);zd(c[q>>2]|0,3);o=c[q>>2]|0;Bd(o,Ad(c[q>>2]|0,c[u>>2]|0,c[E>>2]|0,c[y>>2]|0)|0,0);o=c[q>>2]|0;t=Ad(c[q>>2]|0,c[u>>2]|0,c[F>>2]|0,c[x>>2]|0)|0;Bd(o,t,c[A>>2]|0);t=c[q>>2]|0;o=Ad(c[q>>2]|0,c[u>>2]|0,c[G>>2]|0,c[y>>2]|0)|0;Bd(t,o,c[z>>2]|0);c[j>>2]=(c[j>>2]|0)+1}c[k>>2]=(c[k>>2]|0)+1}mh(c[u>>2]|0);if((c[c[q>>2]>>2]|0)>(c[v>>2]|0)){Ca(576,248,1705,1056)}if((c[(c[q>>2]|0)+16>>2]|0)>(c[w>>2]|0)){Ca(608,248,1706,1056)}I=c[q>>2]|0;ud(I);J=c[q>>2]|0;i=e;return J|0}function fd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;e=i;i=i+64|0;f=e+52|0;g=e+48|0;h=e+40|0;j=e+36|0;k=e+32|0;l=e+28|0;m=e+24|0;n=e+20|0;o=e+16|0;p=e+12|0;q=e+8|0;r=e+4|0;s=e;c[f>>2]=a;c[g>>2]=b;c[e+44>>2]=d;c[k>>2]=15;c[l>>2]=26;c[m>>2]=Z((c[f>>2]|0)*3|0,c[g>>2]|0)|0;c[n>>2]=Z((c[f>>2]|0)+1<<1,(c[g>>2]|0)+1|0)|0;c[p>>2]=rd()|0;c[(c[p>>2]|0)+40>>2]=18;d=_f((c[m>>2]|0)*24|0)|0;c[(c[p>>2]|0)+4>>2]=d;d=_f((c[n>>2]|0)*20|0)|0;c[(c[p>>2]|0)+20>>2]=d;c[o>>2]=lh(8)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[g>>2]|0)){break}c[h>>2]=0;while(1){if((c[h>>2]|0)>=(c[f>>2]|0)){break}c[r>>2]=Z((c[k>>2]|0)+(c[l>>2]|0)|0,c[h>>2]|0)|0;c[s>>2]=Z((c[k>>2]|0)+(c[l>>2]|0)|0,c[j>>2]|0)|0;zd(c[p>>2]|0,4);d=c[p>>2]|0;b=c[o>>2]|0;a=c[r>>2]|0;if((((c[h>>2]|0)+(c[j>>2]|0)|0)%2|0|0)!=0){c[q>>2]=Ad(d,b,a+(c[k>>2]|0)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3)}else{c[q>>2]=Ad(d,b,a+(c[l>>2]|0)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3)}do{if((c[h>>2]|0)>0){zd(c[p>>2]|0,3);a=c[p>>2]|0;b=c[o>>2]|0;d=c[r>>2]|0;if((((c[h>>2]|0)+(c[j>>2]|0)|0)%2|0|0)!=0){c[q>>2]=Ad(a,b,d+(c[k>>2]|0)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);break}else{c[q>>2]=Ad(a,b,d,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);break}}}while(0);do{if((c[j>>2]|0)>0){zd(c[p>>2]|0,3);d=c[p>>2]|0;b=c[o>>2]|0;a=c[r>>2]|0;if((((c[h>>2]|0)+(c[j>>2]|0)|0)%2|0|0)!=0){c[q>>2]=Ad(d,b,a+(c[k>>2]|0)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)-(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);break}else{c[q>>2]=Ad(d,b,a,(c[s>>2]|0)-(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]|0)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);break}}}while(0);c[h>>2]=(c[h>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+1}mh(c[o>>2]|0);if((c[c[p>>2]>>2]|0)>(c[m>>2]|0)){Ca(576,248,1820,1032)}if((c[(c[p>>2]|0)+16>>2]|0)<=(c[n>>2]|0)){ud(c[p>>2]|0);i=e;return c[p>>2]|0}else{Ca(608,248,1821,1032)}return 0}function gd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;e=i;i=i+64|0;f=e+52|0;g=e+48|0;h=e+40|0;j=e+36|0;k=e+32|0;l=e+28|0;m=e+24|0;n=e+20|0;o=e+16|0;p=e+12|0;q=e+8|0;r=e+4|0;s=e;c[f>>2]=a;c[g>>2]=b;c[e+44>>2]=d;c[k>>2]=14;c[l>>2]=31;c[m>>2]=Z(c[f>>2]<<1,c[g>>2]|0)|0;c[n>>2]=Z(((c[f>>2]|0)+1|0)*3|0,(c[g>>2]|0)+1|0)|0;c[p>>2]=rd()|0;c[(c[p>>2]|0)+40>>2]=40;d=_f((c[m>>2]|0)*24|0)|0;c[(c[p>>2]|0)+4>>2]=d;d=_f((c[n>>2]|0)*20|0)|0;c[(c[p>>2]|0)+20>>2]=d;c[o>>2]=lh(8)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[g>>2]|0)){break}c[h>>2]=0;while(1){if((c[h>>2]|0)>=(c[f>>2]|0)){break}c[r>>2]=Z(c[l>>2]<<1,c[h>>2]|0)|0;c[s>>2]=Z(c[l>>2]<<1,c[j>>2]|0)|0;do{if((c[j>>2]|0)>0){zd(c[p>>2]|0,5);d=c[p>>2]|0;b=c[o>>2]|0;a=c[r>>2]|0;if((((c[h>>2]|0)+(c[j>>2]|0)|0)%2|0|0)!=0){c[q>>2]=Ad(d,b,a+(c[k>>2]|0)|0,(c[s>>2]|0)-(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]<<1)-(c[k>>2]|0)|0,(c[s>>2]|0)-(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]<<1)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,4);break}else{c[q>>2]=Ad(d,b,a,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)-(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]<<1)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]<<1)-(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,4);break}}}while(0);do{if((c[h>>2]|0)>0){zd(c[p>>2]|0,5);a=(((c[h>>2]|0)+(c[j>>2]|0)|0)%2|0|0)!=0;c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);b=c[p>>2]|0;d=c[o>>2]|0;t=c[r>>2]|0;if(a){c[q>>2]=Ad(b,d,t+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]<<1)-(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)+(c[l>>2]<<1)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,4);break}else{c[q>>2]=Ad(b,d,t+(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)+(c[l>>2]<<1)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[l>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]<<1)-(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,4);break}}}while(0);c[h>>2]=(c[h>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+1}mh(c[o>>2]|0);if((c[c[p>>2]>>2]|0)>(c[m>>2]|0)){Ca(576,248,1926,1016)}if((c[(c[p>>2]|0)+16>>2]|0)<=(c[n>>2]|0)){ud(c[p>>2]|0);i=e;return c[p>>2]|0}else{Ca(608,248,1927,1016)}return 0}function hd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;e=i;i=i+64|0;f=e+52|0;g=e+48|0;h=e+40|0;j=e+36|0;k=e+32|0;l=e+28|0;m=e+24|0;n=e+20|0;o=e+16|0;p=e+12|0;q=e+8|0;r=e+4|0;s=e;c[f>>2]=a;c[g>>2]=b;c[e+44>>2]=d;c[k>>2]=15;c[l>>2]=26;c[m>>2]=Z(((c[f>>2]|0)+1|0)*6|0,(c[g>>2]|0)+1|0)|0;c[n>>2]=Z((c[f>>2]|0)*6|0,c[g>>2]|0)|0;c[p>>2]=rd()|0;c[(c[p>>2]|0)+40>>2]=18;d=_f((c[m>>2]|0)*24|0)|0;c[(c[p>>2]|0)+4>>2]=d;d=_f((c[n>>2]|0)*20|0)|0;c[(c[p>>2]|0)+20>>2]=d;c[o>>2]=lh(8)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[g>>2]|0)){break}c[h>>2]=0;while(1){if((c[h>>2]|0)>=(c[f>>2]|0)){break}c[r>>2]=Z(((c[k>>2]|0)*3|0)+(c[l>>2]|0)|0,c[h>>2]|0)|0;c[s>>2]=Z((c[k>>2]<<1)+(c[l>>2]<<1)|0,c[j>>2]|0)|0;if(((c[h>>2]|0)%2|0|0)!=0){c[s>>2]=(c[s>>2]|0)+((c[k>>2]|0)+(c[l>>2]|0))}zd(c[p>>2]|0,6);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)-(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)-(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]<<1)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]<<1)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,5);if((c[j>>2]|0)<((c[g>>2]|0)-1|0)){zd(c[p>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]<<1)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]<<1)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3)}do{if((c[h>>2]|0)<((c[f>>2]|0)-1|0)){if(((c[h>>2]|0)%2|0|0)!=0?(c[j>>2]|0)>=((c[g>>2]|0)-1|0):0){break}zd(c[p>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]<<1)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]<<1)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3)}}while(0);do{if((c[h>>2]|0)>0){if(((c[h>>2]|0)%2|0|0)!=0?(c[j>>2]|0)>=((c[g>>2]|0)-1|0):0){break}zd(c[p>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]<<1)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)-(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]<<1)-(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3)}}while(0);if((c[h>>2]|0)<((c[f>>2]|0)-1|0)?(c[j>>2]|0)<((c[g>>2]|0)-1|0):0){zd(c[p>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]<<1)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2)}if((c[h>>2]|0)>0?(c[j>>2]|0)<((c[g>>2]|0)-1|0):0){zd(c[p>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]<<1)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)-(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2)}c[h>>2]=(c[h>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+1}mh(c[o>>2]|0);if((c[c[p>>2]>>2]|0)>(c[m>>2]|0)){Ca(576,248,2056,992)}if((c[(c[p>>2]|0)+16>>2]|0)<=(c[n>>2]|0)){ud(c[p>>2]|0);i=e;return c[p>>2]|0}else{Ca(608,248,2057,992)}return 0}function id(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;e=i;i=i+64|0;f=e+52|0;g=e+48|0;h=e+40|0;j=e+36|0;k=e+32|0;l=e+28|0;m=e+24|0;n=e+20|0;o=e+16|0;p=e+12|0;q=e+8|0;r=e+4|0;s=e;c[f>>2]=a;c[g>>2]=b;c[e+44>>2]=d;c[k>>2]=29;c[l>>2]=41;c[m>>2]=Z(c[f>>2]<<1,c[g>>2]|0)|0;c[n>>2]=Z((c[f>>2]|0)+1<<2,(c[g>>2]|0)+1|0)|0;c[p>>2]=rd()|0;c[(c[p>>2]|0)+40>>2]=40;d=_f((c[m>>2]|0)*24|0)|0;c[(c[p>>2]|0)+4>>2]=d;d=_f((c[n>>2]|0)*20|0)|0;c[(c[p>>2]|0)+20>>2]=d;c[o>>2]=lh(8)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[g>>2]|0)){break}c[h>>2]=0;while(1){if((c[h>>2]|0)>=(c[f>>2]|0)){break}c[r>>2]=Z((c[k>>2]<<1)+(c[l>>2]|0)|0,c[h>>2]|0)|0;c[s>>2]=Z((c[k>>2]<<1)+(c[l>>2]|0)|0,c[j>>2]|0)|0;zd(c[p>>2]|0,8);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]<<1)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]<<1)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]<<1)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]<<1)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,5);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)+(c[k>>2]|0)+(c[l>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,6);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,7);if((c[h>>2]|0)>0?(c[j>>2]|0)>0:0){zd(c[p>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)-(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3)}c[h>>2]=(c[h>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+1}mh(c[o>>2]|0);if((c[c[p>>2]>>2]|0)>(c[m>>2]|0)){Ca(576,248,2139,968)}if((c[(c[p>>2]|0)+16>>2]|0)<=(c[n>>2]|0)){ud(c[p>>2]|0);i=e;return c[p>>2]|0}else{Ca(608,248,2140,968)}return 0}function jd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;e=i;i=i+64|0;f=e+52|0;g=e+48|0;h=e+40|0;j=e+36|0;k=e+32|0;l=e+28|0;m=e+24|0;n=e+20|0;o=e+16|0;p=e+12|0;q=e+8|0;r=e+4|0;s=e;c[f>>2]=a;c[g>>2]=b;c[e+44>>2]=d;c[k>>2]=15;c[l>>2]=26;c[m>>2]=Z((c[f>>2]|0)*6|0,c[g>>2]|0)|0;c[n>>2]=Z(((c[f>>2]|0)+1|0)*6|0,(c[g>>2]|0)+1|0)|0;c[p>>2]=rd()|0;c[(c[p>>2]|0)+40>>2]=40;d=_f((c[m>>2]|0)*24|0)|0;c[(c[p>>2]|0)+4>>2]=d;d=_f((c[n>>2]|0)*20|0)|0;c[(c[p>>2]|0)+20>>2]=d;c[o>>2]=lh(8)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[g>>2]|0)){break}c[h>>2]=0;while(1){if((c[h>>2]|0)>=(c[f>>2]|0)){break}c[r>>2]=Z(c[l>>2]<<2,c[h>>2]|0)|0;c[s>>2]=Z((c[k>>2]|0)*6|0,c[j>>2]|0)|0;if(((c[j>>2]|0)%2|0|0)!=0){c[r>>2]=(c[r>>2]|0)+(c[l>>2]<<1)}zd(c[p>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]<<1)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]<<1)|0,(c[s>>2]|0)+(c[k>>2]<<1)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]|0)*3|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);zd(c[p>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]|0)*3|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)+(c[k>>2]<<2)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[l>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]|0)*3|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);zd(c[p>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[l>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]|0)*3|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[l>>2]<<1)|0,(c[s>>2]|0)+(c[k>>2]<<1)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[l>>2]<<1)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);zd(c[p>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[l>>2]<<1)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[l>>2]<<1)|0,(c[s>>2]|0)-(c[k>>2]<<1)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[l>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]|0)*3|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);zd(c[p>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[l>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]|0)*3|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)-(c[k>>2]<<2)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]|0)*3|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);zd(c[p>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]|0)*3|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]<<1)|0,(c[s>>2]|0)-(c[k>>2]<<1)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[l>>2]<<1)|0,c[s>>2]|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);c[h>>2]=(c[h>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+1}mh(c[o>>2]|0);if((c[c[p>>2]>>2]|0)>(c[m>>2]|0)){Ca(576,248,2259,952)}if((c[(c[p>>2]|0)+16>>2]|0)<=(c[n>>2]|0)){ud(c[p>>2]|0);i=e;return c[p>>2]|0}else{Ca(608,248,2260,952)}return 0}function kd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0;e=i;i=i+80|0;f=e+68|0;g=e+64|0;h=e+56|0;j=e+52|0;k=e+48|0;l=e+44|0;m=e+40|0;n=e+36|0;o=e+32|0;p=e+28|0;q=e+24|0;r=e+20|0;s=e+16|0;t=e+12|0;u=e+8|0;v=e+4|0;w=e;c[f>>2]=a;c[g>>2]=b;c[e+60>>2]=d;c[k>>2]=75;c[l>>2]=-26;c[m>>2]=(c[k>>2]<<2|0)/5|0;c[n>>2]=0-(c[l>>2]|0)<<1;c[o>>2]=(c[m>>2]|0)-(c[k>>2]|0);c[p>>2]=(c[n>>2]|0)-(c[l>>2]|0);c[q>>2]=Z((c[f>>2]|0)*6|0,c[g>>2]|0)|0;c[r>>2]=Z(((c[f>>2]|0)+1|0)*9|0,(c[g>>2]|0)+1|0)|0;c[t>>2]=rd()|0;c[(c[t>>2]|0)+40>>2]=150;d=_f((c[q>>2]|0)*24|0)|0;c[(c[t>>2]|0)+4>>2]=d;d=_f((c[r>>2]|0)*20|0)|0;c[(c[t>>2]|0)+20>>2]=d;c[s>>2]=lh(8)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[g>>2]|0)){break}c[h>>2]=0;while(1){if((c[h>>2]|0)>=(c[f>>2]|0)){break}c[v>>2]=Z((((c[k>>2]|0)*6|0)+((c[m>>2]|0)*3|0)|0)/2|0,c[h>>2]|0)|0;c[w>>2]=Z((c[l>>2]<<2)-((c[n>>2]|0)*5|0)|0,c[j>>2]|0)|0;if(((c[h>>2]|0)%2|0|0)==0){if(!((c[j>>2]|0)!=0?(c[j>>2]|0)==((c[g>>2]|0)-1|0):0)){x=9}}else{c[w>>2]=(c[w>>2]|0)-(((c[l>>2]<<2)-((c[n>>2]|0)*5|0)|0)/2|0);x=9}if((x|0)==9){x=0;zd(c[t>>2]|0,5);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,c[v>>2]|0,c[w>>2]|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,0);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)+(c[o>>2]<<1)|0,(c[w>>2]|0)+(c[p>>2]<<1)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,1);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)+(c[o>>2]<<1)+(c[m>>2]|0)|0,(c[w>>2]|0)+(c[p>>2]<<1)+(c[n>>2]|0)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,2);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)+(c[m>>2]<<1)+(c[o>>2]|0)|0,(c[w>>2]|0)+(c[n>>2]<<1)+(c[p>>2]|0)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,3);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)+(c[m>>2]<<1)|0,(c[w>>2]|0)+(c[n>>2]<<1)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,4);zd(c[t>>2]|0,5);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,c[v>>2]|0,c[w>>2]|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,0);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)+(c[m>>2]<<1)|0,(c[w>>2]|0)+(c[n>>2]<<1)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,1);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)+(c[m>>2]<<1)+(c[k>>2]|0)|0,(c[w>>2]|0)+(c[n>>2]<<1)+(c[l>>2]|0)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,2);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)+(c[k>>2]<<1)+(c[m>>2]|0)|0,(c[w>>2]|0)+(c[l>>2]<<1)+(c[n>>2]|0)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,3);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)+(c[k>>2]<<1)|0,(c[w>>2]|0)+(c[l>>2]<<1)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,4);zd(c[t>>2]|0,5);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,c[v>>2]|0,c[w>>2]|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,0);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)+(c[k>>2]<<1)|0,(c[w>>2]|0)+(c[l>>2]<<1)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,1);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)+(c[k>>2]<<1)-(c[o>>2]|0)|0,(c[w>>2]|0)+(c[l>>2]<<1)-(c[p>>2]|0)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,2);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)-(c[o>>2]<<1)+(c[k>>2]|0)|0,(c[w>>2]|0)-(c[p>>2]<<1)+(c[l>>2]|0)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,3);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)-(c[o>>2]<<1)|0,(c[w>>2]|0)-(c[p>>2]<<1)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,4);zd(c[t>>2]|0,5);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,c[v>>2]|0,c[w>>2]|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,0);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)-(c[o>>2]<<1)|0,(c[w>>2]|0)-(c[p>>2]<<1)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,1);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)-(c[o>>2]<<1)-(c[m>>2]|0)|0,(c[w>>2]|0)-(c[p>>2]<<1)-(c[n>>2]|0)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,2);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)-(c[m>>2]<<1)-(c[o>>2]|0)|0,(c[w>>2]|0)-(c[n>>2]<<1)-(c[p>>2]|0)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,3);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)-(c[m>>2]<<1)|0,(c[w>>2]|0)-(c[n>>2]<<1)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,4);zd(c[t>>2]|0,5);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,c[v>>2]|0,c[w>>2]|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,0);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)-(c[m>>2]<<1)|0,(c[w>>2]|0)-(c[n>>2]<<1)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,1);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)-(c[m>>2]<<1)-(c[k>>2]|0)|0,(c[w>>2]|0)-(c[n>>2]<<1)-(c[l>>2]|0)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,2);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)-(c[k>>2]<<1)-(c[m>>2]|0)|0,(c[w>>2]|0)-(c[l>>2]<<1)-(c[n>>2]|0)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,3);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)-(c[k>>2]<<1)|0,(c[w>>2]|0)-(c[l>>2]<<1)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,4);zd(c[t>>2]|0,5);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,c[v>>2]|0,c[w>>2]|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,0);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)-(c[k>>2]<<1)|0,(c[w>>2]|0)-(c[l>>2]<<1)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,1);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)-(c[k>>2]<<1)+(c[o>>2]|0)|0,(c[w>>2]|0)-(c[l>>2]<<1)+(c[p>>2]|0)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,2);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)+(c[o>>2]<<1)-(c[k>>2]|0)|0,(c[w>>2]|0)+(c[p>>2]<<1)-(c[l>>2]|0)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,3);c[u>>2]=Ad(c[t>>2]|0,c[s>>2]|0,(c[v>>2]|0)+(c[o>>2]<<1)|0,(c[w>>2]|0)+(c[p>>2]<<1)|0)|0;Bd(c[t>>2]|0,c[u>>2]|0,4)}c[h>>2]=(c[h>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+1}mh(c[s>>2]|0);if((c[c[t>>2]>>2]|0)>(c[q>>2]|0)){Ca(576,248,2367,936)}if((c[(c[t>>2]|0)+16>>2]|0)<=(c[r>>2]|0)){ud(c[t>>2]|0);i=e;return c[t>>2]|0}else{Ca(608,248,2368,936)}return 0}function ld(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;e=i;i=i+64|0;f=e+52|0;g=e+48|0;h=e+40|0;j=e+36|0;k=e+32|0;l=e+28|0;m=e+24|0;n=e+20|0;o=e+16|0;p=e+12|0;q=e+8|0;r=e+4|0;s=e;c[f>>2]=a;c[g>>2]=b;c[e+44>>2]=d;c[k>>2]=15;c[l>>2]=26;c[m>>2]=Z((c[f>>2]|0)*3|0,c[g>>2]|0)|0;c[n>>2]=Z((c[f>>2]|0)*14|0,c[g>>2]|0)|0;c[p>>2]=rd()|0;c[(c[p>>2]|0)+40>>2]=26;d=_f((c[m>>2]|0)*24|0)|0;c[(c[p>>2]|0)+4>>2]=d;d=_f((c[n>>2]|0)*20|0)|0;c[(c[p>>2]|0)+20>>2]=d;c[o>>2]=lh(8)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[g>>2]|0)){break}c[h>>2]=0;while(1){if((c[h>>2]|0)>=(c[f>>2]|0)){break}c[r>>2]=Z((c[k>>2]<<2)+(c[l>>2]<<1)|0,c[h>>2]|0)|0;c[s>>2]=Z(((c[k>>2]|0)*3|0)+(c[l>>2]<<1)|0,c[j>>2]|0)|0;if(((c[j>>2]|0)%2|0|0)!=0){c[r>>2]=(c[r>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))}zd(c[p>>2]|0,12);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+((c[k>>2]|0)+(c[l>>2]|0))|0,(c[s>>2]|0)-((c[k>>2]|0)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))|0,(c[s>>2]|0)-(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+((c[k>>2]|0)+(c[l>>2]|0))|0,(c[s>>2]|0)+((c[k>>2]|0)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,5);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,6);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-((c[k>>2]|0)+(c[l>>2]|0))|0,(c[s>>2]|0)+((c[k>>2]|0)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,7);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,8);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0,(c[s>>2]|0)-(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,9);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-((c[k>>2]|0)+(c[l>>2]|0))|0,(c[s>>2]|0)-((c[k>>2]|0)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,10);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,11);do{if((c[j>>2]|0)<((c[g>>2]|0)-1|0)){if((c[h>>2]|0)>=((c[f>>2]|0)-1|0)?((c[j>>2]|0)%2|0|0)!=0:0){break}if((c[h>>2]|0)<=0?((c[j>>2]|0)%2|0|0)==0:0){break}zd(c[p>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)+((c[k>>2]<<1)+(c[l>>2]<<1))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2)}}while(0);do{if((c[j>>2]|0)!=0){if((c[h>>2]|0)>=((c[f>>2]|0)-1|0)?((c[j>>2]|0)%2|0|0)!=0:0){break}if((c[h>>2]|0)<=0?((c[j>>2]|0)%2|0|0)==0:0){break}zd(c[p>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,c[r>>2]|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]<<1))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2)}}while(0);c[h>>2]=(c[h>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+1}mh(c[o>>2]|0);if((c[c[p>>2]>>2]|0)>(c[m>>2]|0)){Ca(576,248,2453,912)}if((c[(c[p>>2]|0)+16>>2]|0)<=(c[n>>2]|0)){ud(c[p>>2]|0);i=e;return c[p>>2]|0}else{Ca(608,248,2454,912)}return 0}function md(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;e=i;i=i+64|0;f=e+52|0;g=e+48|0;h=e+40|0;j=e+36|0;k=e+32|0;l=e+28|0;m=e+24|0;n=e+20|0;o=e+16|0;p=e+12|0;q=e+8|0;r=e+4|0;s=e;c[f>>2]=a;c[g>>2]=b;c[e+44>>2]=d;c[k>>2]=15;c[l>>2]=26;c[m>>2]=Z((c[f>>2]|0)*30|0,c[g>>2]|0)|0;c[n>>2]=Z((c[f>>2]|0)*200|0,c[g>>2]|0)|0;c[p>>2]=rd()|0;c[(c[p>>2]|0)+40>>2]=26;d=_f((c[m>>2]|0)*24|0)|0;c[(c[p>>2]|0)+4>>2]=d;d=_f((c[n>>2]|0)*20|0)|0;c[(c[p>>2]|0)+20>>2]=d;c[o>>2]=lh(8)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[g>>2]|0)){break}c[h>>2]=0;while(1){if((c[h>>2]|0)>=(c[f>>2]|0)){break}c[r>>2]=Z(((c[k>>2]|0)*6|0)+(c[l>>2]<<1)|0,c[h>>2]|0)|0;c[s>>2]=Z(((c[k>>2]|0)*3|0)+((c[l>>2]|0)*3|0)|0,c[j>>2]|0)|0;if(((c[j>>2]|0)%2|0|0)!=0){c[r>>2]=(c[r>>2]|0)+(((c[k>>2]|0)*3|0)+(c[l>>2]|0))}zd(c[p>>2]|0,12);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+((c[k>>2]|0)+(c[l>>2]|0))|0,(c[s>>2]|0)-((c[k>>2]|0)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))|0,(c[s>>2]|0)-(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+((c[k>>2]|0)+(c[l>>2]|0))|0,(c[s>>2]|0)+((c[k>>2]|0)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,5);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,6);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-((c[k>>2]|0)+(c[l>>2]|0))|0,(c[s>>2]|0)+((c[k>>2]|0)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,7);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,8);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0,(c[s>>2]|0)-(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,9);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-((c[k>>2]|0)+(c[l>>2]|0))|0,(c[s>>2]|0)-((c[k>>2]|0)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,10);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,11);do{if((c[j>>2]|0)<((c[g>>2]|0)-1|0)){if((c[h>>2]|0)>=((c[f>>2]|0)-1|0)?((c[j>>2]|0)%2|0|0)!=0:0){break}if((c[h>>2]|0)<=0?((c[j>>2]|0)%2|0|0)==0:0){break}zd(c[p>>2]|0,6);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]<<1)|0,(c[s>>2]|0)+((c[k>>2]<<1)+(c[l>>2]<<1))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]<<1)+((c[l>>2]|0)*3|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]<<1)+((c[l>>2]|0)*3|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]<<1)|0,(c[s>>2]|0)+((c[k>>2]<<1)+(c[l>>2]<<1))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,5)}}while(0);do{if((c[j>>2]|0)!=0){if((c[h>>2]|0)>=((c[f>>2]|0)-1|0)?((c[j>>2]|0)%2|0|0)!=0:0){break}if((c[h>>2]|0)<=0?((c[j>>2]|0)%2|0|0)==0:0){break}zd(c[p>>2]|0,6);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]<<1)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]<<1))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]<<1)+((c[l>>2]|0)*3|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]<<1)+((c[l>>2]|0)*3|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]<<1)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]<<1))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,5)}}while(0);if((c[h>>2]|0)<((c[f>>2]|0)-1|0)){zd(c[p>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]<<1)+(c[l>>2]|0)|0,(c[s>>2]|0)-(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]<<2)+(c[l>>2]|0)|0,(c[s>>2]|0)-(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]<<2)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]<<1)+(c[l>>2]|0)|0,(c[s>>2]|0)+(c[k>>2]|0)|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3)}do{if((c[j>>2]|0)!=0){if((c[h>>2]|0)>=((c[f>>2]|0)-1|0)?((c[j>>2]|0)%2|0|0)!=0:0){break}zd(c[p>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+(c[k>>2]<<1)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]<<1))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+((c[k>>2]<<1)+(c[l>>2]|0))|0,(c[s>>2]|0)-((c[k>>2]|0)+(c[l>>2]<<1))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)+((c[k>>2]|0)+(c[l>>2]|0))|0,(c[s>>2]|0)-((c[k>>2]|0)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3)}}while(0);do{if((c[j>>2]|0)!=0){if((c[h>>2]|0)==0?((c[j>>2]|0)%2|0|0)==0:0){break}zd(c[p>>2]|0,4);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-((c[k>>2]|0)+(c[l>>2]|0))|0,(c[s>>2]|0)-((c[k>>2]|0)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,0);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0,(c[s>>2]|0)-((c[k>>2]|0)+(c[l>>2]<<1))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,1);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]<<1)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]<<1))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,2);c[q>>2]=Ad(c[p>>2]|0,c[o>>2]|0,(c[r>>2]|0)-(c[k>>2]|0)|0,(c[s>>2]|0)-((c[k>>2]<<1)+(c[l>>2]|0))|0)|0;Bd(c[p>>2]|0,c[q>>2]|0,3)}}while(0);c[h>>2]=(c[h>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+1}mh(c[o>>2]|0);if((c[c[p>>2]>>2]|0)>(c[m>>2]|0)){Ca(576,248,2567,880)}if((c[(c[p>>2]|0)+16>>2]|0)<=(c[n>>2]|0)){ud(c[p>>2]|0);i=e;return c[p>>2]|0}else{Ca(608,248,2568,880)}return 0}function nd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0;e=i;i=i+16|0;f=e+8|0;g=e+4|0;h=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;d=pd(c[f>>2]|0,c[g>>2]|0,0,c[h>>2]|0)|0;i=e;return d|0}function od(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0;e=i;i=i+16|0;f=e+8|0;g=e+4|0;h=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;d=pd(c[f>>2]|0,c[g>>2]|0,1,c[h>>2]|0)|0;i=e;return d|0}function pd(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0;f=i;i=i+128|0;g=f+8|0;h=f+120|0;j=f+116|0;k=f+112|0;l=f+108|0;m=f+104|0;n=f+100|0;o=f+96|0;p=f+92|0;q=f+88|0;r=f+84|0;s=f+80|0;t=f+76|0;u=f+72|0;v=f+68|0;w=f+64|0;x=f+48|0;y=f+24|0;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[p>>2]=100;Wg(c[l>>2]|0,c[p>>2]|0,c[j>>2]|0,c[k>>2]|0,f,x,x+4|0);c[x+8>>2]=3;c[x+12>>2]=y;c[n>>2]=Z((c[j>>2]|0)*3|0,(c[k>>2]|0)*3|0)|0;c[o>>2]=c[n>>2]<<2;c[w>>2]=rd()|0;c[(c[w>>2]|0)+40>>2]=c[p>>2];e=_f((c[n>>2]|0)*24|0)|0;c[(c[w>>2]|0)+4>>2]=e;e=_f((c[o>>2]|0)*20|0)|0;c[(c[w>>2]|0)+20>>2]=e;c[v>>2]=lh(8)|0;c[y+0>>2]=0;c[y+4>>2]=0;c[y+8>>2]=0;c[y+12>>2]=0;c[y+16>>2]=0;c[y+20>>2]=0;c[y+16>>2]=c[w>>2];c[y+20>>2]=c[v>>2];if((c[m>>2]|0)!=0){e=c[m>>2]|0;c[g>>2]=s;c[g+4>>2]=t;c[g+8>>2]=u;if((Ka(e|0,536,g|0)|0)!=3){Ca(376,248,2767,552)}}else{c[u>>2]=0;c[t>>2]=0;c[s>>2]=0}c[q>>2]=Z(c[j>>2]|0,c[p>>2]|0)|0;c[r>>2]=Z(c[k>>2]|0,c[p>>2]|0)|0;c[y>>2]=(c[s>>2]|0)-((c[q>>2]|0)/2|0);c[y+4>>2]=(c[s>>2]|0)+((c[q>>2]|0)/2|0);c[y+8>>2]=(c[t>>2]|0)-((c[r>>2]|0)/2|0);c[y+12>>2]=(c[t>>2]|0)+((c[r>>2]|0)/2|0);Qg(x,c[l>>2]|0,c[u>>2]|0)|0;mh(c[v>>2]|0);if((c[c[w>>2]>>2]|0)>(c[n>>2]|0)){Ca(576,248,2788,552)}if((c[(c[w>>2]|0)+16>>2]|0)>(c[o>>2]|0)){Ca(608,248,2789,552)}if((c[c[w>>2]>>2]|0)!=0?(c[(c[w>>2]|0)+16>>2]|0)!=0:0){td(c[w>>2]|0);if((c[c[w>>2]>>2]|0)!=0?(c[(c[w>>2]|0)+16>>2]|0)!=0:0){ud(c[w>>2]|0);o=(c[w>>2]|0)+24|0;c[o>>2]=(c[o>>2]|0)-(((c[y+4>>2]|0)-(c[y>>2]|0)-((c[(c[w>>2]|0)+32>>2]|0)-(c[(c[w>>2]|0)+24>>2]|0))|0)/2|0);c[(c[w>>2]|0)+32>>2]=(c[(c[w>>2]|0)+24>>2]|0)+((c[y+4>>2]|0)-(c[y>>2]|0));o=(c[w>>2]|0)+28|0;c[o>>2]=(c[o>>2]|0)-(((c[y+12>>2]|0)-(c[y+8>>2]|0)-((c[(c[w>>2]|0)+36>>2]|0)-(c[(c[w>>2]|0)+28>>2]|0))|0)/2|0);c[(c[w>>2]|0)+36>>2]=(c[(c[w>>2]|0)+28>>2]|0)+((c[y+12>>2]|0)-(c[y+8>>2]|0));c[h>>2]=c[w>>2];z=c[h>>2]|0;i=f;return z|0}Dc(c[w>>2]|0);c[h>>2]=0;z=c[h>>2]|0;i=f;return z|0}Dc(c[w>>2]|0);c[h>>2]=0;z=c[h>>2]|0;i=f;return z|0}function qd(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0;f=i;i=i+96|0;g=f+80|0;j=f+76|0;k=f+72|0;l=f+68|0;m=f+64|0;n=f+60|0;o=f+56|0;p=f+40|0;q=f+24|0;r=f+8|0;s=f;t=f+16|0;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=c[(c[j>>2]|0)+12>>2];if((c[m>>2]|0)<(c[(c[j>>2]|0)+4>>2]|0)){c[g>>2]=0;u=c[g>>2]|0;i=f;return u|0}c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[l>>2]|0)){v=12;break}h[r>>3]=+Og(c[k>>2]|0,c[o>>2]|0);h[s>>3]=+Pg(c[k>>2]|0,c[o>>2]|0);j=~~+yd(+h[r>>3]);c[p+(c[o>>2]<<2)>>2]=j;j=~~+yd(+h[s>>3]);c[q+(c[o>>2]<<2)>>2]=j;if((c[p+(c[o>>2]<<2)>>2]|0)<(c[c[n>>2]>>2]|0)){v=7;break}if((c[p+(c[o>>2]<<2)>>2]|0)>(c[(c[n>>2]|0)+4>>2]|0)){v=7;break}if((c[q+(c[o>>2]<<2)>>2]|0)<(c[(c[n>>2]|0)+8>>2]|0)){v=10;break}if((c[q+(c[o>>2]<<2)>>2]|0)>(c[(c[n>>2]|0)+12>>2]|0)){v=10;break}c[o>>2]=(c[o>>2]|0)+1}if((v|0)==7){c[g>>2]=0;u=c[g>>2]|0;i=f;return u|0}else if((v|0)==10){c[g>>2]=0;u=c[g>>2]|0;i=f;return u|0}else if((v|0)==12){zd(c[(c[n>>2]|0)+16>>2]|0,c[l>>2]|0);c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[l>>2]|0)){break}c[t>>2]=Ad(c[(c[n>>2]|0)+16>>2]|0,c[(c[n>>2]|0)+20>>2]|0,c[p+(c[o>>2]<<2)>>2]|0,c[q+(c[o>>2]<<2)>>2]|0)|0;Bd(c[(c[n>>2]|0)+16>>2]|0,c[t>>2]|0,c[o>>2]|0);c[o>>2]=(c[o>>2]|0)+1}c[g>>2]=0;u=c[g>>2]|0;i=f;return u|0}return 0}function rd(){var a=0,b=0;a=i;i=i+16|0;b=a;c[b>>2]=_f(48)|0;c[(c[b>>2]|0)+4>>2]=0;c[(c[b>>2]|0)+12>>2]=0;c[(c[b>>2]|0)+20>>2]=0;c[(c[b>>2]|0)+16>>2]=0;c[(c[b>>2]|0)+8>>2]=0;c[c[b>>2]>>2]=0;c[(c[b>>2]|0)+44>>2]=1;c[(c[b>>2]|0)+36>>2]=0;c[(c[b>>2]|0)+32>>2]=0;c[(c[b>>2]|0)+28>>2]=0;c[(c[b>>2]|0)+24>>2]=0;i=a;return c[b>>2]|0}function sd(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0;d=i;i=i+32|0;e=d+16|0;f=d+12|0;g=d+8|0;h=d+4|0;j=d;c[f>>2]=a;c[g>>2]=b;c[h>>2]=c[f>>2];c[j>>2]=c[g>>2];g=c[j>>2]|0;if((c[(c[h>>2]|0)+16>>2]|0)!=(c[(c[j>>2]|0)+16>>2]|0)){c[e>>2]=(c[g+16>>2]|0)-(c[(c[h>>2]|0)+16>>2]|0);k=c[e>>2]|0;i=d;return k|0}else{c[e>>2]=(c[g+12>>2]|0)-(c[(c[h>>2]|0)+12>>2]|0);k=c[e>>2]|0;i=d;return k|0}return 0}function td(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0;b=i;i=i+96|0;d=b+80|0;e=b+76|0;f=b+72|0;g=b+68|0;h=b+64|0;j=b+60|0;k=b+56|0;l=b+52|0;m=b+48|0;n=b+44|0;o=b+40|0;p=b+36|0;q=b+32|0;r=b+28|0;s=b+24|0;t=b+20|0;u=b+16|0;v=b+12|0;w=b+8|0;x=b+4|0;y=b;c[d>>2]=a;c[e>>2]=_f((Z(c[(c[d>>2]|0)+16>>2]|0,c[(c[d>>2]|0)+16>>2]|0)|0)<<2)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){break}c[k>>2]=0;while(1){z=c[j>>2]|0;if((c[k>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){break}a=Z(z,c[(c[d>>2]|0)+16>>2]|0)|0;c[(c[e>>2]|0)+(a+(c[k>>2]|0)<<2)>>2]=-1;c[k>>2]=(c[k>>2]|0)+1}c[j>>2]=z+1}c[j>>2]=0;while(1){A=c[d>>2]|0;if((c[j>>2]|0)>=(c[c[d>>2]>>2]|0)){break}c[p>>2]=(c[A+4>>2]|0)+((c[j>>2]|0)*24|0);c[q>>2]=((c[(c[(c[p>>2]|0)+8>>2]|0)+((c[c[p>>2]>>2]|0)-1<<2)>>2]|0)-(c[(c[d>>2]|0)+20>>2]|0)|0)/20|0;c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[c[p>>2]>>2]|0)){break}c[r>>2]=((c[(c[(c[p>>2]|0)+8>>2]|0)+(c[k>>2]<<2)>>2]|0)-(c[(c[d>>2]|0)+20>>2]|0)|0)/20|0;z=Z(c[q>>2]|0,c[(c[d>>2]|0)+16>>2]|0)|0;c[(c[e>>2]|0)+(z+(c[r>>2]|0)<<2)>>2]=c[j>>2];c[q>>2]=c[r>>2];c[k>>2]=(c[k>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+1}c[g>>2]=_f(c[A+16>>2]<<2)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){break}c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]=1;c[k>>2]=0;while(1){B=c[j>>2]|0;if((c[k>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){break}A=Z(B,c[(c[d>>2]|0)+16>>2]|0)|0;r=Z(c[k>>2]|0,c[(c[d>>2]|0)+16>>2]|0)|0;if(((c[(c[e>>2]|0)+(A+(c[k>>2]|0)<<2)>>2]|0)>=0^(c[(c[e>>2]|0)+(r+(c[j>>2]|0)<<2)>>2]|0)>=0|0)!=0){c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]=0}c[k>>2]=(c[k>>2]|0)+1}c[j>>2]=B+1}c[h>>2]=xc(c[(c[d>>2]|0)+16>>2]|0)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){break}c[k>>2]=0;while(1){C=c[j>>2]|0;if((c[k>>2]|0)>=(c[j>>2]|0)){break}if((((c[(c[g>>2]|0)+(C<<2)>>2]|0)!=0?(c[(c[g>>2]|0)+(c[k>>2]<<2)>>2]|0)!=0:0)?(B=Z(c[j>>2]|0,c[(c[d>>2]|0)+16>>2]|0)|0,(c[(c[e>>2]|0)+(B+(c[k>>2]|0)<<2)>>2]|0)>=0):0)?(B=Z(c[k>>2]|0,c[(c[d>>2]|0)+16>>2]|0)|0,(c[(c[e>>2]|0)+(B+(c[j>>2]|0)<<2)>>2]|0)>=0):0){Ac(c[h>>2]|0,c[j>>2]|0,c[k>>2]|0)}c[k>>2]=(c[k>>2]|0)+1}c[j>>2]=C+1}c[m>>2]=0;c[k>>2]=-1;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){break}if(((c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]|0)!=0?(C=yc(c[h>>2]|0,c[j>>2]|0)|0,(C|0)==(c[j>>2]|0)):0)?(C=Cc(c[h>>2]|0,c[j>>2]|0)|0,c[s>>2]=C,(C|0)>(c[m>>2]|0)):0){c[k>>2]=c[j>>2];c[m>>2]=c[s>>2]}c[j>>2]=(c[j>>2]|0)+1}c[f>>2]=_f(c[c[d>>2]>>2]<<2)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[c[d>>2]>>2]|0)){break}c[(c[f>>2]|0)+(c[j>>2]<<2)>>2]=0;c[j>>2]=(c[j>>2]|0)+1}c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){break}c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]=0;c[j>>2]=(c[j>>2]|0)+1}c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[c[d>>2]>>2]|0)){break}c[t>>2]=(c[(c[d>>2]|0)+4>>2]|0)+((c[j>>2]|0)*24|0);c[u>>2]=0;c[l>>2]=0;while(1){if((c[l>>2]|0)>=(c[c[t>>2]>>2]|0)){break}s=yc(c[h>>2]|0,((c[(c[(c[t>>2]|0)+8>>2]|0)+(c[l>>2]<<2)>>2]|0)-(c[(c[d>>2]|0)+20>>2]|0)|0)/20|0)|0;if((s|0)==(c[k>>2]|0)){c[u>>2]=1}c[l>>2]=(c[l>>2]|0)+1}a:do{if((c[u>>2]|0)!=0){c[(c[f>>2]|0)+(c[j>>2]<<2)>>2]=1;c[l>>2]=0;while(1){if((c[l>>2]|0)>=(c[c[t>>2]>>2]|0)){break a}c[(c[g>>2]|0)+((((c[(c[(c[t>>2]|0)+8>>2]|0)+(c[l>>2]<<2)>>2]|0)-(c[(c[d>>2]|0)+20>>2]|0)|0)/20|0)<<2)>>2]=1;c[l>>2]=(c[l>>2]|0)+1}}}while(0);c[j>>2]=(c[j>>2]|0)+1}c[n>>2]=0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[c[d>>2]>>2]|0)){break}if((c[(c[f>>2]|0)+(c[j>>2]<<2)>>2]|0)!=0){t=c[n>>2]|0;c[n>>2]=t+1;D=t}else{D=-1}c[(c[f>>2]|0)+(c[j>>2]<<2)>>2]=D;c[j>>2]=(c[j>>2]|0)+1}c[o>>2]=0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){break}if((c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]|0)!=0){D=c[o>>2]|0;c[o>>2]=D+1;E=D}else{E=-1}c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]=E;c[j>>2]=(c[j>>2]|0)+1}c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[c[d>>2]>>2]|0)){break}if((c[(c[f>>2]|0)+(c[j>>2]<<2)>>2]|0)<0){$f(c[(c[(c[d>>2]|0)+4>>2]|0)+((c[j>>2]|0)*24|0)+8>>2]|0)}c[j>>2]=(c[j>>2]|0)+1}c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){break}if((c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]|0)>=0){c[v>>2]=(c[(c[d>>2]|0)+20>>2]|0)+((c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]|0)*20|0);c[w>>2]=(c[(c[d>>2]|0)+20>>2]|0)+((c[j>>2]|0)*20|0);E=c[v>>2]|0;D=c[w>>2]|0;c[E+0>>2]=c[D+0>>2];c[E+4>>2]=c[D+4>>2];c[E+8>>2]=c[D+8>>2];c[E+12>>2]=c[D+12>>2];c[E+16>>2]=c[D+16>>2]}c[j>>2]=(c[j>>2]|0)+1}c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[c[d>>2]>>2]|0)){break}b:do{if((c[(c[f>>2]|0)+(c[j>>2]<<2)>>2]|0)>=0){c[x>>2]=(c[(c[d>>2]|0)+4>>2]|0)+((c[(c[f>>2]|0)+(c[j>>2]<<2)>>2]|0)*24|0);c[y>>2]=(c[(c[d>>2]|0)+4>>2]|0)+((c[j>>2]|0)*24|0);w=c[x>>2]|0;v=c[y>>2]|0;c[w+0>>2]=c[v+0>>2];c[w+4>>2]=c[v+4>>2];c[w+8>>2]=c[v+8>>2];c[w+12>>2]=c[v+12>>2];c[w+16>>2]=c[v+16>>2];c[w+20>>2]=c[v+20>>2];c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[c[x>>2]>>2]|0)){break b}c[l>>2]=((c[(c[(c[x>>2]|0)+8>>2]|0)+(c[k>>2]<<2)>>2]|0)-(c[(c[d>>2]|0)+20>>2]|0)|0)/20|0;c[(c[(c[x>>2]|0)+8>>2]|0)+(c[k>>2]<<2)>>2]=(c[(c[d>>2]|0)+20>>2]|0)+((c[(c[g>>2]|0)+(c[l>>2]<<2)>>2]|0)*20|0);c[k>>2]=(c[k>>2]|0)+1}}}while(0);c[j>>2]=(c[j>>2]|0)+1}c[c[d>>2]>>2]=c[n>>2];c[(c[d>>2]|0)+16>>2]=c[o>>2];$f(c[e>>2]|0);$f(c[h>>2]|0);$f(c[g>>2]|0);$f(c[f>>2]|0);i=b;return}function ud(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0,L=0,M=0,N=0,O=0,P=0,Q=0,R=0,S=0;b=i;i=i+144|0;d=b+140|0;e=b+136|0;f=b+132|0;g=b+128|0;h=b+124|0;j=b+120|0;k=b+104|0;l=b+96|0;m=b+92|0;n=b+88|0;o=b+84|0;p=b+80|0;q=b+76|0;r=b+72|0;s=b+68|0;t=b+64|0;u=b+60|0;v=b+56|0;w=b+52|0;x=b+48|0;y=b+44|0;z=b+40|0;A=b+36|0;B=b+32|0;C=b+28|0;D=b+24|0;E=b+20|0;F=b+16|0;G=b+12|0;H=b+8|0;I=b+4|0;J=b;c[d>>2]=a;vd(c[d>>2]|0);c[(c[d>>2]|0)+8>>2]=(c[c[d>>2]>>2]|0)+(c[(c[d>>2]|0)+16>>2]|0)-1;a=_f(c[(c[d>>2]|0)+8>>2]<<4)|0;c[(c[d>>2]|0)+12>>2]=a;c[g>>2]=c[(c[d>>2]|0)+12>>2];c[f>>2]=lh(9)|0;c[e>>2]=0;a:while(1){if((c[e>>2]|0)>=(c[c[d>>2]>>2]|0)){break}c[h>>2]=(c[(c[d>>2]|0)+4>>2]|0)+((c[e>>2]|0)*24|0);c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[c[h>>2]>>2]|0)){break}a=(c[j>>2]|0)+1|0;c[m>>2]=a;c[m>>2]=(c[m>>2]|0)==(c[c[h>>2]>>2]|0)?0:a;c[k>>2]=c[(c[(c[h>>2]|0)+8>>2]|0)+(c[j>>2]<<2)>>2];c[k+4>>2]=c[(c[(c[h>>2]|0)+8>>2]|0)+(c[m>>2]<<2)>>2];c[l>>2]=wh(c[f>>2]|0,k)|0;if((c[l>>2]|0)!=0){c[(c[l>>2]|0)+12>>2]=c[h>>2]}else{if((((c[g>>2]|0)-(c[(c[d>>2]|0)+12>>2]|0)|0)/16|0|0)>=(c[(c[d>>2]|0)+8>>2]|0)){K=8;break a}c[c[g>>2]>>2]=c[k>>2];c[(c[g>>2]|0)+4>>2]=c[k+4>>2];c[(c[g>>2]|0)+8>>2]=c[h>>2];c[(c[g>>2]|0)+12>>2]=0;qh(c[f>>2]|0,c[g>>2]|0)|0;c[g>>2]=(c[g>>2]|0)+16}c[j>>2]=(c[j>>2]|0)+1}c[e>>2]=(c[e>>2]|0)+1}if((K|0)==8){Ca(632,248,551,672)}mh(c[f>>2]|0);c[e>>2]=0;while(1){if((c[e>>2]|0)>=(c[c[d>>2]>>2]|0)){break}c[n>>2]=(c[(c[d>>2]|0)+4>>2]|0)+((c[e>>2]|0)*24|0);f=_f(c[c[n>>2]>>2]<<2)|0;c[(c[n>>2]|0)+4>>2]=f;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[c[n>>2]>>2]|0)){break}c[(c[(c[n>>2]|0)+4>>2]|0)+(c[o>>2]<<2)>>2]=0;c[o>>2]=(c[o>>2]|0)+1}c[e>>2]=(c[e>>2]|0)+1}c[e>>2]=0;b:while(1){if((c[e>>2]|0)>=(c[(c[d>>2]|0)+8>>2]|0)){K=45;break}c[p>>2]=(c[(c[d>>2]|0)+12>>2]|0)+(c[e>>2]<<4);c[q>>2]=0;while(1){if((c[q>>2]|0)>=2){break}o=c[p>>2]|0;if((c[q>>2]|0)!=0){L=c[o+12>>2]|0}else{L=c[o+8>>2]|0}c[r>>2]=L;do{if((c[r>>2]|0)!=0){c[s>>2]=0;while(1){if((c[s>>2]|0)>=(c[c[r>>2]>>2]|0)){break}if((c[(c[(c[r>>2]|0)+8>>2]|0)+(c[s>>2]<<2)>>2]|0)==(c[c[p>>2]>>2]|0)){break}c[s>>2]=(c[s>>2]|0)+1}if((c[s>>2]|0)==(c[c[r>>2]>>2]|0)){K=31;break b}o=(c[s>>2]|0)+1|0;c[t>>2]=o;c[t>>2]=(c[t>>2]|0)==(c[c[r>>2]>>2]|0)?0:o;o=c[s>>2]|0;if((c[(c[(c[r>>2]|0)+8>>2]|0)+(c[t>>2]<<2)>>2]|0)==(c[(c[p>>2]|0)+4>>2]|0)){if((c[(c[(c[r>>2]|0)+4>>2]|0)+(o<<2)>>2]|0)!=0){K=34;break b}c[(c[(c[r>>2]|0)+4>>2]|0)+(c[s>>2]<<2)>>2]=c[p>>2];break}c[t>>2]=o-1;if((c[t>>2]|0)==-1){c[t>>2]=(c[c[r>>2]>>2]|0)-1}if((c[(c[(c[r>>2]|0)+8>>2]|0)+(c[t>>2]<<2)>>2]|0)!=(c[(c[p>>2]|0)+4>>2]|0)){K=42;break b}if((c[(c[(c[r>>2]|0)+4>>2]|0)+(c[t>>2]<<2)>>2]|0)!=0){K=40;break b}c[(c[(c[r>>2]|0)+4>>2]|0)+(c[t>>2]<<2)>>2]=c[p>>2]}}while(0);c[q>>2]=(c[q>>2]|0)+1}c[e>>2]=(c[e>>2]|0)+1}if((K|0)==31){Ca(696,248,593,672)}else if((K|0)==34){Ca(712,248,618,672)}else if((K|0)==40){Ca(736,248,628,672)}else if((K|0)==42){Ca(760,248,632,672)}else if((K|0)==45){c[e>>2]=0;while(1){if((c[e>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){break}c[(c[(c[d>>2]|0)+20>>2]|0)+((c[e>>2]|0)*20|0)>>2]=0;c[e>>2]=(c[e>>2]|0)+1}c[e>>2]=0;while(1){if((c[e>>2]|0)>=(c[(c[d>>2]|0)+8>>2]|0)){break}c[u>>2]=(c[(c[d>>2]|0)+12>>2]|0)+(c[e>>2]<<4);q=c[c[u>>2]>>2]|0;c[q>>2]=(c[q>>2]|0)+1;q=c[(c[u>>2]|0)+4>>2]|0;c[q>>2]=(c[q>>2]|0)+1;c[e>>2]=(c[e>>2]|0)+1}c[e>>2]=0;while(1){if((c[e>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){break}c[v>>2]=(c[(c[d>>2]|0)+20>>2]|0)+((c[e>>2]|0)*20|0);if((c[c[v>>2]>>2]|0)<2){K=54;break}u=_f(c[c[v>>2]>>2]<<2)|0;c[(c[v>>2]|0)+4>>2]=u;u=_f(c[c[v>>2]>>2]<<2)|0;c[(c[v>>2]|0)+8>>2]=u;c[w>>2]=0;while(1){if((c[w>>2]|0)>=(c[c[v>>2]>>2]|0)){break}c[(c[(c[v>>2]|0)+4>>2]|0)+(c[w>>2]<<2)>>2]=0;c[(c[(c[v>>2]|0)+8>>2]|0)+(c[w>>2]<<2)>>2]=0;c[w>>2]=(c[w>>2]|0)+1}c[e>>2]=(c[e>>2]|0)+1}if((K|0)==54){Ca(808,248,655,672)}c[e>>2]=0;while(1){if((c[e>>2]|0)>=(c[c[d>>2]>>2]|0)){break}c[x>>2]=(c[(c[d>>2]|0)+4>>2]|0)+((c[e>>2]|0)*24|0);c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[c[x>>2]>>2]|0)){break}c[z>>2]=c[(c[(c[x>>2]|0)+8>>2]|0)+(c[y>>2]<<2)>>2];c[c[(c[z>>2]|0)+8>>2]>>2]=c[x>>2];c[y>>2]=(c[y>>2]|0)+1}c[e>>2]=(c[e>>2]|0)+1}c[e>>2]=0;c:while(1){if((c[e>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){K=102;break}c[A>>2]=(c[(c[d>>2]|0)+20>>2]|0)+((c[e>>2]|0)*20|0);c[B>>2]=0;c[C>>2]=0;do{c[D>>2]=c[(c[(c[A>>2]|0)+8>>2]|0)+(c[B>>2]<<2)>>2];if((c[D>>2]|0)==0){K=69;break c}c[F>>2]=0;while(1){if((c[F>>2]|0)>=(c[c[D>>2]>>2]|0)){break}if((c[(c[(c[D>>2]|0)+8>>2]|0)+(c[F>>2]<<2)>>2]|0)==(c[A>>2]|0)){break}c[F>>2]=(c[F>>2]|0)+1}if((c[F>>2]|0)==(c[c[D>>2]>>2]|0)){K=75;break c}c[F>>2]=(c[F>>2]|0)+ -1;if((c[F>>2]|0)==-1){c[F>>2]=(c[c[D>>2]>>2]|0)-1}c[E>>2]=c[(c[(c[D>>2]|0)+4>>2]|0)+(c[F>>2]<<2)>>2];c[(c[(c[A>>2]|0)+4>>2]|0)+(c[B>>2]<<2)>>2]=c[E>>2];c[B>>2]=(c[B>>2]|0)+1;if((c[B>>2]|0)==(c[c[A>>2]>>2]|0)){break}y=c[E>>2]|0;if((c[(c[E>>2]|0)+8>>2]|0)==(c[D>>2]|0)){M=c[y+12>>2]|0}else{M=c[y+8>>2]|0}c[(c[(c[A>>2]|0)+8>>2]|0)+(c[B>>2]<<2)>>2]=M}while((c[(c[(c[A>>2]|0)+8>>2]|0)+(c[B>>2]<<2)>>2]|0)!=0);d:do{if((c[B>>2]|0)!=(c[c[A>>2]>>2]|0)){while(1){c[G>>2]=c[(c[(c[A>>2]|0)+8>>2]|0)+(c[C>>2]<<2)>>2];if((c[G>>2]|0)==0){K=85;break c}c[I>>2]=0;while(1){if((c[I>>2]|0)>=(c[c[G>>2]>>2]|0)){break}if((c[(c[(c[G>>2]|0)+8>>2]|0)+(c[I>>2]<<2)>>2]|0)==(c[A>>2]|0)){break}c[I>>2]=(c[I>>2]|0)+1}if((c[I>>2]|0)==(c[c[G>>2]>>2]|0)){K=91;break c}c[H>>2]=c[(c[(c[G>>2]|0)+4>>2]|0)+(c[I>>2]<<2)>>2];c[C>>2]=(c[C>>2]|0)+ -1;if((c[C>>2]|0)==-1){c[C>>2]=(c[c[A>>2]>>2]|0)-1}c[(c[(c[A>>2]|0)+4>>2]|0)+(c[C>>2]<<2)>>2]=c[H>>2];if((c[C>>2]|0)==(c[B>>2]|0)){break d}y=c[H>>2]|0;if((c[(c[H>>2]|0)+8>>2]|0)==(c[G>>2]|0)){N=c[y+12>>2]|0}else{N=c[y+8>>2]|0}c[(c[(c[A>>2]|0)+8>>2]|0)+(c[C>>2]<<2)>>2]=N;if((c[(c[(c[A>>2]|0)+8>>2]|0)+(c[C>>2]<<2)>>2]|0)==0){K=99;break c}}}}while(0);c[e>>2]=(c[e>>2]|0)+1}if((K|0)==69){Ca(824,248,707,672)}else if((K|0)==75){Ca(840,248,713,672)}else if((K|0)==85){Ca(824,248,744,672)}else if((K|0)==91){Ca(840,248,750,672)}else if((K|0)==99){Ca(856,248,767,672)}else if((K|0)==102){c[e>>2]=0;while(1){O=c[d>>2]|0;if((c[e>>2]|0)>=(c[(c[d>>2]|0)+16>>2]|0)){break}c[J>>2]=(c[O+20>>2]|0)+((c[e>>2]|0)*20|0);if((c[e>>2]|0)==0){K=c[(c[J>>2]|0)+12>>2]|0;c[(c[d>>2]|0)+32>>2]=K;c[(c[d>>2]|0)+24>>2]=K;K=c[(c[J>>2]|0)+16>>2]|0;c[(c[d>>2]|0)+36>>2]=K;c[(c[d>>2]|0)+28>>2]=K}else{if((c[(c[d>>2]|0)+24>>2]|0)<(c[(c[J>>2]|0)+12>>2]|0)){P=c[(c[d>>2]|0)+24>>2]|0}else{P=c[(c[J>>2]|0)+12>>2]|0}c[(c[d>>2]|0)+24>>2]=P;if((c[(c[d>>2]|0)+32>>2]|0)>(c[(c[J>>2]|0)+12>>2]|0)){Q=c[(c[d>>2]|0)+32>>2]|0}else{Q=c[(c[J>>2]|0)+12>>2]|0}c[(c[d>>2]|0)+32>>2]=Q;if((c[(c[d>>2]|0)+28>>2]|0)<(c[(c[J>>2]|0)+16>>2]|0)){R=c[(c[d>>2]|0)+28>>2]|0}else{R=c[(c[J>>2]|0)+16>>2]|0}c[(c[d>>2]|0)+28>>2]=R;if((c[(c[d>>2]|0)+36>>2]|0)>(c[(c[J>>2]|0)+16>>2]|0)){S=c[(c[d>>2]|0)+36>>2]|0}else{S=c[(c[J>>2]|0)+16>>2]|0}c[(c[d>>2]|0)+36>>2]=S}c[e>>2]=(c[e>>2]|0)+1}xd(O);i=b;return}}}function vd(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;i=b;return}function wd(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0;d=i;i=i+32|0;e=d+24|0;f=d+20|0;g=d+16|0;h=d+12|0;j=d+8|0;k=d+4|0;l=d;c[f>>2]=a;c[g>>2]=b;c[h>>2]=c[f>>2];c[j>>2]=c[g>>2];g=c[h>>2]|0;if((c[c[h>>2]>>2]|0)>>>0<(c[(c[h>>2]|0)+4>>2]|0)>>>0){m=c[g>>2]|0}else{m=c[g+4>>2]|0}c[k>>2]=m;m=c[j>>2]|0;if((c[c[j>>2]>>2]|0)>>>0<(c[(c[j>>2]|0)+4>>2]|0)>>>0){n=c[m>>2]|0}else{n=c[m+4>>2]|0}c[l>>2]=n;if((c[k>>2]|0)!=(c[l>>2]|0)){c[e>>2]=((c[l>>2]|0)-(c[k>>2]|0)|0)/20|0;o=c[e>>2]|0;i=d;return o|0}n=c[h>>2]|0;if((c[c[h>>2]>>2]|0)>>>0<(c[(c[h>>2]|0)+4>>2]|0)>>>0){p=c[n+4>>2]|0}else{p=c[n>>2]|0}c[k>>2]=p;p=c[j>>2]|0;if((c[c[j>>2]>>2]|0)>>>0<(c[(c[j>>2]|0)+4>>2]|0)>>>0){q=c[p+4>>2]|0}else{q=c[p>>2]|0}c[l>>2]=q;if((c[k>>2]|0)!=(c[l>>2]|0)){c[e>>2]=((c[l>>2]|0)-(c[k>>2]|0)|0)/20|0;o=c[e>>2]|0;i=d;return o|0}else{c[e>>2]=0;o=c[e>>2]|0;i=d;return o|0}return 0}function xd(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;i=b;return}function yd(a){a=+a;var b=0,c=0,d=0.0;b=i;i=i+16|0;c=b;h[c>>3]=a;a=+h[c>>3];if(+h[c>>3]>0.0){d=+L(+(a+.5));i=b;return+d}else{d=+Y(+(a-.5));i=b;return+d}return 0.0}function zd(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0;d=i;i=i+16|0;e=d+12|0;f=d+8|0;g=d+4|0;h=d;c[e>>2]=a;c[f>>2]=b;c[h>>2]=(c[(c[e>>2]|0)+4>>2]|0)+((c[c[e>>2]>>2]|0)*24|0);c[c[h>>2]>>2]=c[f>>2];b=_f(c[f>>2]<<2)|0;c[(c[h>>2]|0)+8>>2]=b;c[g>>2]=0;while(1){if((c[g>>2]|0)>=(c[f>>2]|0)){break}c[(c[(c[h>>2]|0)+8>>2]|0)+(c[g>>2]<<2)>>2]=0;c[g>>2]=(c[g>>2]|0)+1}c[(c[h>>2]|0)+4>>2]=0;c[(c[h>>2]|0)+12>>2]=0;h=c[e>>2]|0;c[h>>2]=(c[h>>2]|0)+1;i=d;return}function Ad(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;f=i;i=i+48|0;g=f+40|0;h=f+36|0;j=f+32|0;k=f+28|0;l=f+24|0;m=f+4|0;n=f;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=0;c[m+4>>2]=0;c[m+8>>2]=0;c[m+12>>2]=c[k>>2];c[m+16>>2]=c[l>>2];c[n>>2]=uh(c[j>>2]|0,m,0)|0;if((c[n>>2]|0)!=0){c[g>>2]=c[n>>2];o=c[g>>2]|0;i=f;return o|0}else{c[n>>2]=Cd(c[h>>2]|0,c[k>>2]|0,c[l>>2]|0)|0;qh(c[j>>2]|0,c[n>>2]|0)|0;c[g>>2]=c[n>>2];o=c[g>>2]|0;i=f;return o|0}return 0}function Bd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0;e=i;i=i+16|0;f=e+12|0;g=e+8|0;h=e+4|0;j=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;c[j>>2]=(c[(c[f>>2]|0)+4>>2]|0)+((c[c[f>>2]>>2]|0)*24|0)+ -24;c[(c[(c[j>>2]|0)+8>>2]|0)+(c[h>>2]<<2)>>2]=c[g>>2];i=e;return}function Cd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0;e=i;i=i+16|0;f=e+12|0;g=e+8|0;h=e+4|0;j=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;c[j>>2]=(c[(c[f>>2]|0)+20>>2]|0)+((c[(c[f>>2]|0)+16>>2]|0)*20|0);c[c[j>>2]>>2]=0;c[(c[j>>2]|0)+4>>2]=0;c[(c[j>>2]|0)+8>>2]=0;c[(c[j>>2]|0)+12>>2]=c[g>>2];c[(c[j>>2]|0)+16>>2]=c[h>>2];h=(c[f>>2]|0)+16|0;c[h>>2]=(c[h>>2]|0)+1;i=e;return c[j>>2]|0}function Dd(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;g=d;c[e>>2]=a;c[f>>2]=b;c[g>>2]=_f(8)|0;gb(c[g>>2]|0);c[c[e>>2]>>2]=c[g>>2];c[c[f>>2]>>2]=8;i=d;return}function Ed(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0;d=i;i=i+544|0;e=d+16|0;f=d+24|0;g=d;c[e>>2]=a;Rh(f|0,1360)|0;c[g>>2]=b;b=f+(Nh(f|0)|0)|0;a=512-(Nh(f|0)|0)|0;kb(b|0,a|0,c[e>>2]|0,g|0)|0;ua(f|0);i=d;return}function Fd(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;g=d;c[f>>2]=a;c[g>>2]=b;if((c[f>>2]|0)!=0?(c[g>>2]|0)!=0:0){c[e>>2]=Lh(c[f>>2]|0,c[g>>2]|0)|0;h=c[e>>2]|0;i=d;return h|0}if((c[f>>2]|0)!=0){j=1}else{j=(c[g>>2]|0)!=0?-1:0}c[e>>2]=j;h=c[e>>2]|0;i=d;return h|0}function Gd(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;jb();c[346]=0;i=b;return}function Hd(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;if((c[346]|0)!=0){i=b;return}mb();c[346]=1;i=b;return}function Id(a){a=+a;var b=0,d=0;b=i;i=i+16|0;d=b;h[d>>3]=a;if((c[346]|0)==0){i=b;return}ug(c[348]|0,+h[d>>3]);i=b;return}function Jd(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;fg(c[348]|0,e,f,1);if((c[350]|0)==(c[e>>2]|0)?(c[352]|0)==(c[f>>2]|0):0){i=d;return}Fa(c[e>>2]|0,c[f>>2]|0);c[350]=c[e>>2];c[352]=c[f>>2];ig(c[348]|0);i=d;return}function Kd(a,b){a=a|0;b=b|0;var d=0;d=i;i=i+16|0;c[d+4>>2]=a;c[d>>2]=b;cg(c[348]|0);Ld();ig(c[348]|0);i=d;return}function Ld(){var a=0,b=0,d=0;a=i;i=i+16|0;b=a+4|0;d=a;c[d>>2]=2147483647;c[b>>2]=2147483647;fg(c[348]|0,b,d,0);Fa(c[b>>2]|0,c[d>>2]|0);c[350]=c[b>>2];c[352]=c[d>>2];i=a;return}function Md(a,b){a=a|0;b=b|0;var d=0,e=0;d=i;i=i+16|0;e=d;c[d+4>>2]=a;c[e>>2]=b;g[(c[e>>2]|0)+8>>2]=.8999999761581421;g[(c[e>>2]|0)+4>>2]=.8999999761581421;g[c[e>>2]>>2]=.8999999761581421;i=d;return}function Nd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0;e=i;i=i+16|0;f=e+8|0;g=e+4|0;h=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;if((c[h>>2]|0)==0){j=512}else{j=(c[h>>2]|0)==1?513:514}c[h>>2]=j;sg(c[348]|0,c[f>>2]|0,c[g>>2]|0,c[h>>2]|0)|0;Od();i=e;return}function Od(){var a=0,b=0;a=i;b=ng(c[348]|0)|0;eb(b|0,og(c[348]|0)|0);i=a;return}function Pd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0;e=i;i=i+16|0;f=e+8|0;g=e+4|0;h=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;if((c[h>>2]|0)==0){j=518}else{j=(c[h>>2]|0)==1?519:520}c[h>>2]=j;sg(c[348]|0,c[f>>2]|0,c[g>>2]|0,c[h>>2]|0)|0;Od();i=e;return}function Qd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0;e=i;i=i+16|0;f=e+12|0;g=e+8|0;h=e+4|0;j=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;if((c[h>>2]&2|0)!=0){k=516}else{k=(c[h>>2]&4|0)!=0?517:515}c[j>>2]=k;sg(c[348]|0,c[f>>2]|0,c[g>>2]|0,c[j>>2]|0)|0;Od();i=e;return}function Rd(b,d,e,f,g,h){b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;var j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0;j=i;i=i+32|0;k=j+24|0;l=j+16|0;m=j+12|0;n=j+8|0;o=j+4|0;p=j;c[k>>2]=b;c[j+20>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=g;c[o>>2]=h;c[p>>2]=-1;do{if(((Fd(c[l>>2]|0,1416)|0)!=0?(Fd(c[l>>2]|0,1432)|0)!=0:0)?!((c[k>>2]|0)==8|(c[k>>2]|0)==46):0){if((Fd(c[l>>2]|0,1440)|0)!=0?(c[k>>2]|0)!=13:0){if((Fd(c[l>>2]|0,1448)|0)!=0?(c[k>>2]|0)!=37:0){if((Fd(c[l>>2]|0,1456)|0)!=0?(c[k>>2]|0)!=38:0){if((Fd(c[l>>2]|0,1464)|0)!=0?(c[k>>2]|0)!=39:0){if((Fd(c[l>>2]|0,1472)|0)!=0?(c[k>>2]|0)!=40:0){if((Fd(c[l>>2]|0,1480)|0)!=0?(c[k>>2]|0)!=35:0){if((Fd(c[l>>2]|0,1488)|0)!=0?(c[k>>2]|0)!=34:0){if((Fd(c[l>>2]|0,1504)|0)!=0?(c[k>>2]|0)!=36:0){if((Fd(c[l>>2]|0,1512)|0)!=0?(c[k>>2]|0)!=33:0){if(((c[m>>2]|0)!=0?(a[c[m>>2]|0]|0)!=0:0)?(a[(c[m>>2]|0)+1|0]|0)==0:0){c[p>>2]=a[c[m>>2]|0]&255;break}h=c[k>>2]|0;if((c[k>>2]|0)>=96&(c[k>>2]|0)<106){c[p>>2]=16384|48+h-96;break}g=c[k>>2]|0;if((h|0)>=65&(c[k>>2]|0)<=90){c[p>>2]=g+((c[n>>2]|0)!=0?0:32);break}h=c[k>>2]|0;if((g|0)>=48&(c[k>>2]|0)<=57){c[p>>2]=h;break}if((h|0)!=32){break}c[p>>2]=c[k>>2];break}c[p>>2]=16441;break}c[p>>2]=16439;break}c[p>>2]=16435;break}c[p>>2]=16433;break}c[p>>2]=522;break}c[p>>2]=524;break}c[p>>2]=521;break}c[p>>2]=523;break}c[p>>2]=13}else{q=4}}while(0);if((q|0)==4){c[p>>2]=127}if((c[p>>2]|0)<0){i=j;return}if((c[n>>2]|0)!=0?(c[p>>2]|0)>=256:0){c[p>>2]=c[p>>2]|8192}do{if((c[o>>2]|0)!=0){n=c[p>>2]|0;if((c[p>>2]|0)>=256){c[p>>2]=n|4096;break}else{c[p>>2]=n&31;break}}}while(0);sg(c[348]|0,0,0,c[p>>2]|0)|0;Od();i=j;return}function Sd(a,b,d,e,f,g,h,j){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0;k=i;i=i+128|0;l=k;m=k+36|0;n=k+32|0;o=k+28|0;p=k+24|0;q=k+20|0;r=k+16|0;s=k+12|0;t=k+48|0;u=k+8|0;c[k+40>>2]=a;c[m>>2]=b;c[n>>2]=d;c[o>>2]=e;c[p>>2]=f;c[q>>2]=g;c[r>>2]=h;c[s>>2]=j;j=(c[o>>2]|0)==0?1736:1752;c[l>>2]=c[p>>2];c[l+4>>2]=j;cb(t|0,1728,l|0)|0;if((c[q>>2]&256|0)!=0){l=Ba(c[p>>2]|0,t|0)|0;c[n>>2]=(c[n>>2]|0)+l}do{if((c[q>>2]&1|0)==0){if((c[q>>2]&2|0)!=0){c[u>>2]=2;break}else{c[u>>2]=0;break}}else{c[u>>2]=1}}while(0);Wa(c[m>>2]|0,c[n>>2]|0,c[u>>2]|0,c[(c[424]|0)+(c[r>>2]<<2)>>2]|0,t|0,c[s>>2]|0);i=k;return}function Td(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0;h=i;i=i+32|0;j=h+16|0;k=h+12|0;l=h+8|0;m=h+4|0;n=h;c[h+20>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=g;Ja(c[j>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0,c[(c[424]|0)+(c[n>>2]<<2)>>2]|0);i=h;return}function Ud(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0;h=i;i=i+32|0;j=h+16|0;k=h+12|0;l=h+8|0;m=h+4|0;n=h;c[h+20>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=g;ya(+(+(c[j>>2]|0)),+(+(c[k>>2]|0)),+(+(c[l>>2]|0)),+(+(c[m>>2]|0)),1,c[(c[424]|0)+(c[n>>2]<<2)>>2]|0);i=h;return}function Vd(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0;g=i;i=i+32|0;h=g+12|0;j=g+8|0;k=g+4|0;l=g;c[g+16>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=f;if((c[k>>2]|0)>=0){m=c[(c[424]|0)+(c[k>>2]<<2)>>2]|0}else{m=0}zb(c[h>>2]|0,c[j>>2]|0,m|0,c[(c[424]|0)+(c[l>>2]<<2)>>2]|0);i=g;return}function Wd(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0;h=i;i=i+32|0;j=h+16|0;k=h+12|0;l=h+8|0;m=h+4|0;n=h;c[h+20>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=g;if((c[m>>2]|0)>=0){o=c[(c[424]|0)+(c[m>>2]<<2)>>2]|0}else{o=0}Ia(c[j>>2]|0,c[k>>2]|0,c[l>>2]|0,o|0,c[(c[424]|0)+(c[n>>2]<<2)>>2]|0);i=h;return}function Xd(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0;g=i;i=i+32|0;h=g+12|0;j=g+8|0;k=g+4|0;l=g;c[g+16>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=f;qe(h,j,k,l);if((c[k>>2]|0)<=0){i=g;return}if((c[l>>2]|0)<=0){i=g;return}Za(c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0);i=g;return}function Yd(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0;g=i;i=i+32|0;h=g+12|0;j=g+8|0;k=g+4|0;l=g;c[g+16>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=f;xb(c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0);i=g;return}function Zd(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;Ua();i=b;return}function _d(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;db();i=b;return}function $d(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;nb();i=b;return}function ae(a,b){a=a|0;b=b|0;var d=0,e=0;d=i;i=i+16|0;e=d;c[d+4>>2]=a;c[e>>2]=b;ub(c[e>>2]|0);i=d;return}function be(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0;e=i;i=i+16|0;f=e+8|0;g=e+4|0;h=e;c[e+12>>2]=a;c[f>>2]=b;c[g>>2]=d;c[h>>2]=_f(12)|0;c[(c[h>>2]|0)+4>>2]=c[f>>2];c[(c[h>>2]|0)+8>>2]=c[g>>2];d=Na(c[f>>2]|0,c[g>>2]|0)|0;c[c[h>>2]>>2]=d;i=e;return c[h>>2]|0}function ce(a,b){a=a|0;b=b|0;var d=0,e=0;d=i;i=i+16|0;e=d;c[d+4>>2]=a;c[e>>2]=b;Ab(c[c[e>>2]>>2]|0);$f(c[e>>2]|0);i=d;return}function de(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0;f=i;i=i+32|0;g=f+16|0;h=f+12|0;j=f+8|0;k=f+4|0;l=f;c[f+20>>2]=a;c[g>>2]=b;c[h>>2]=d;c[j>>2]=e;c[k>>2]=c[(c[g>>2]|0)+4>>2];c[l>>2]=c[(c[g>>2]|0)+8>>2];qe(h,j,k,l);if((c[k>>2]|0)<=0){i=f;return}if((c[l>>2]|0)<=0){i=f;return}rb(c[c[g>>2]>>2]|0,c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0);i=f;return}function ee(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0;f=i;i=i+32|0;g=f+16|0;h=f+12|0;j=f+8|0;k=f+4|0;l=f;c[f+20>>2]=a;c[g>>2]=b;c[h>>2]=d;c[j>>2]=e;c[k>>2]=c[(c[g>>2]|0)+4>>2];c[l>>2]=c[(c[g>>2]|0)+8>>2];qe(h,j,k,l);if((c[k>>2]|0)<=0){i=f;return}if((c[l>>2]|0)<=0){i=f;return}lb(c[c[g>>2]>>2]|0,c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0);i=f;return}function fe(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0;e=i;i=i+16|0;f=e+4|0;c[e+8>>2]=a;c[f>>2]=b;c[e>>2]=d;d=bg(c[c[f>>2]>>2]|0)|0;i=e;return d|0}function ge(a,b,d,e,f,h,j){a=a|0;b=+b;d=+d;e=+e;f=+f;h=+h;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0;k=i;i=i+32|0;l=k+20|0;m=k+16|0;n=k+12|0;o=k+8|0;p=k+4|0;q=k;c[k+24>>2]=a;g[l>>2]=b;g[m>>2]=d;g[n>>2]=e;g[o>>2]=f;g[p>>2]=h;c[q>>2]=j;ya(+(+g[m>>2]),+(+g[n>>2]),+(+g[o>>2]),+(+g[p>>2]),~~+g[l>>2]|0,c[(c[424]|0)+(c[q>>2]<<2)>>2]|0);i=k;return}function he(){var a=0,b=0;a=i;i=i+16|0;b=a;if((c[406]|0)==0){i=a;return}c[b>>2]=yg(c[348]|0)|0;wa(((c[b>>2]|0)<0?-1:c[b>>2]|0)|0);i=a;return}function ie(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;$f(c[(c[408]|0)+(c[e>>2]<<4)+8>>2]|0);b=bg(c[f>>2]|0)|0;c[(c[408]|0)+(c[e>>2]<<4)+8>>2]=b;i=d;return}function je(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;c[(c[408]|0)+(c[e>>2]<<4)+12>>2]=c[f>>2];i=d;return}function ke(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+8|0;e=b+4|0;f=b;c[d>>2]=a;switch(c[d>>2]|0){case 0:{le(2);i=b;return};case 2:{c[e>>2]=Ha()|0;if((c[e>>2]|0)<0){if((c[2044>>2]|0)==0){i=b;return}le(0);i=b;return}else{if((c[e>>2]|0)>=(c[410]|0)){Ca(1648,1664,692,1672)}hg(c[348]|0,c[(c[420]|0)+(c[e>>2]<<2)>>2]|0);kg(c[348]|0);Ld();jg(c[348]|0);Od();Ea();he();i=b;return}break};case 7:{sg(c[348]|0,0,0,117)|0;Od();Ea();i=b;return};case 8:{sg(c[348]|0,0,0,114)|0;Od();Ea();i=b;return};case 9:{if((c[2080>>2]|0)!=0?(c[f>>2]=Hg(c[348]|0)|0,(c[f>>2]|0)!=0):0){ua(c[f>>2]|0)}Od();Ea();i=b;return};case 6:{qg(c[348]|0);Od();Ea();i=b;return};case 3:{me(1);Od();i=b;return};case 1:{le(1);i=b;return};case 4:{me(0);Od();i=b;return};case 5:{sg(c[348]|0,0,0,110)|0;Od();Ea();i=b;return};default:{i=b;return}}}function le(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+8|0;e=b+4|0;f=b;c[d>>2]=a;c[408]=Bg(c[348]|0,c[d>>2]|0,e)|0;c[430]=c[d>>2];xa(c[e>>2]|0);$f(c[e>>2]|0);c[f>>2]=0;while(1){if((c[(c[408]|0)+(c[f>>2]<<4)+4>>2]|0)==3){break}e=c[(c[408]|0)+(c[f>>2]<<4)+4>>2]|0;if((e|0)==0){Xa(c[f>>2]|0,c[(c[408]|0)+(c[f>>2]<<4)>>2]|0,c[(c[408]|0)+(c[f>>2]<<4)+8>>2]|0)}else if((e|0)==2){Ma(c[f>>2]|0,c[(c[408]|0)+(c[f>>2]<<4)>>2]|0,c[(c[408]|0)+(c[f>>2]<<4)+12>>2]|0)}else if((e|0)==1){qb(c[f>>2]|0,c[(c[408]|0)+(c[f>>2]<<4)>>2]|0,c[(c[408]|0)+(c[f>>2]<<4)+8>>2]|0,c[(c[408]|0)+(c[f>>2]<<4)+12>>2]|0)}c[f>>2]=(c[f>>2]|0)+1}Ga();i=b;return}function me(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;if((c[d>>2]|0)==0){he();Lg(c[408]|0);va();i=b;return}c[e>>2]=Gg(c[348]|0,c[430]|0,c[408]|0)|0;if((c[e>>2]|0)!=0){ua(c[e>>2]|0);i=b;return}else{he();kg(c[348]|0);Ld();jg(c[348]|0);Lg(c[408]|0);va();i=b;return}}function ne(b,d){b=b|0;d=d|0;var e=0,f=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;e=i;i=i+80|0;f=e;h=e+32|0;j=e+28|0;k=e+24|0;l=e+20|0;m=e+16|0;n=e+12|0;o=e+40|0;c[e+36>>2]=0;c[h>>2]=b;c[j>>2]=d;c[348]=dg(0,2008,1520,0)|0;if(((c[h>>2]|0)>1?(a[c[(c[j>>2]|0)+4>>2]|0]|0)==35:0)?(a[(c[(c[j>>2]|0)+4>>2]|0)+1|0]|0)!=0:0){c[k>>2]=Cg(c[348]|0,(c[(c[j>>2]|0)+4>>2]|0)+1|0)|0}else{c[k>>2]=0}kg(c[348]|0);Ld();if((zg(c[348]|0)|0)!=0){Ra()}c[410]=wg(c[348]|0)|0;if((c[410]|0)==0){Sa();c[406]=0}else{c[420]=_f(c[410]<<2)|0;c[m>>2]=0;while(1){if((c[m>>2]|0)>=(c[410]|0)){break}xg(c[348]|0,c[m>>2]|0,n,(c[420]|0)+(c[m>>2]<<2)|0);Bb(c[n>>2]|0);c[m>>2]=(c[m>>2]|0)+1}if((c[2044>>2]|0)!=0){Bb(0)}c[406]=1;he()}if((c[2080>>2]|0)==0){ab()}c[l>>2]=vg(c[348]|0,1688)|0;c[424]=_f(c[422]<<2)|0;c[m>>2]=0;while(1){if((c[m>>2]|0)>=(c[422]|0)){break}n=~~(+g[(c[l>>2]|0)+(((c[m>>2]|0)*3|0)+1<<2)>>2]*255.0+.5)>>>0;j=~~(+g[(c[l>>2]|0)+(((c[m>>2]|0)*3|0)+2<<2)>>2]*255.0+.5)>>>0;c[f>>2]=~~(+g[(c[l>>2]|0)+(((c[m>>2]|0)*3|0)+0<<2)>>2]*255.0+.5)>>>0;c[f+4>>2]=n;c[f+8>>2]=j;cb(o|0,1704,f|0)|0;j=bg(o)|0;c[(c[424]|0)+(c[m>>2]<<2)>>2]=j;c[m>>2]=(c[m>>2]|0)+1}Ag(c[348]|0,7,0);jg(c[348]|0);pe();Od();if((c[k>>2]|0)==0){i=e;return 0}ua(c[k>>2]|0);i=e;return 0}function oe(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;pe();i=b;return}function pe(){var a=0,b=0,d=0;a=i;i=i+16|0;b=a+4|0;d=a;c[b>>2]=Eg(c[348]|0)|0;c[d>>2]=Fg(c[348]|0)|0;_a(c[b>>2]|0,c[d>>2]|0);$f(c[b>>2]|0);$f(c[d>>2]|0);i=a;return}function qe(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;f=i;i=i+32|0;g=f+28|0;h=f+24|0;j=f+20|0;k=f+16|0;l=f+12|0;m=f+8|0;n=f+4|0;o=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=c[c[g>>2]>>2];c[n>>2]=c[c[h>>2]>>2];c[m>>2]=(c[c[g>>2]>>2]|0)+(c[c[j>>2]>>2]|0);c[o>>2]=(c[c[h>>2]>>2]|0)+(c[c[k>>2]>>2]|0);if((c[l>>2]|0)<0){p=0}else{p=(c[l>>2]|0)>(c[350]|0)?c[350]|0:c[l>>2]|0}c[l>>2]=p;if((c[m>>2]|0)<0){q=0}else{q=(c[m>>2]|0)>(c[350]|0)?c[350]|0:c[m>>2]|0}c[m>>2]=q;if((c[n>>2]|0)<0){r=0}else{r=(c[n>>2]|0)>(c[352]|0)?c[352]|0:c[n>>2]|0}c[n>>2]=r;if((c[o>>2]|0)<0){s=0}else{s=(c[o>>2]|0)>(c[352]|0)?c[352]|0:c[o>>2]|0}c[o>>2]=s;c[c[g>>2]>>2]=c[l>>2];c[c[h>>2]>>2]=c[n>>2];c[c[j>>2]>>2]=(c[m>>2]|0)-(c[l>>2]|0);c[c[k>>2]>>2]=(c[o>>2]|0)-(c[n>>2]|0);i=f;return}function re(b,d,e,f,g){b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0,L=0,M=0,N=0,O=0,P=0,Q=0,R=0,S=0;h=i;i=i+144|0;j=h+128|0;k=h+124|0;l=h+120|0;m=h+116|0;n=h+112|0;o=h+108|0;p=h+104|0;q=h+100|0;r=h+96|0;s=h+92|0;t=h+88|0;u=h+84|0;v=h+80|0;w=h+76|0;x=h+72|0;y=h+68|0;z=h+64|0;A=h+60|0;B=h+56|0;C=h+52|0;D=h+48|0;E=h+44|0;F=h+40|0;G=h+36|0;H=h+32|0;I=h+28|0;J=h+24|0;K=h+20|0;L=h+16|0;M=h+12|0;N=h+8|0;O=h+4|0;P=h;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=g;c[q>>2]=c[c[j>>2]>>2];Oh(c[k>>2]|0,1,c[q>>2]|0)|0;c[r>>2]=_f((c[q>>2]|0)*12|0)|0;c[o>>2]=0;while(1){Q=c[l>>2]|0;if((c[o>>2]|0)>=(c[q>>2]|0)){break}g=ih(Q,31)|0;c[(c[r>>2]|0)+((c[o>>2]|0)*12|0)+8>>2]=g;c[(c[r>>2]|0)+((c[o>>2]|0)*12|0)>>2]=0;c[(c[r>>2]|0)+((c[o>>2]|0)*12|0)+4>>2]=0;c[o>>2]=(c[o>>2]|0)+1}c[o>>2]=jh(Q,c[q>>2]|0)|0;a[(c[k>>2]|0)+(c[o>>2]|0)|0]=0;c[u>>2]=lh(10)|0;c[v>>2]=lh(11)|0;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[q>>2]|0)){break}c[y>>2]=(c[(c[j>>2]|0)+4>>2]|0)+((c[o>>2]|0)*24|0);c[z>>2]=(c[r>>2]|0)+((c[o>>2]|0)*12|0);if((a[(c[k>>2]|0)+(c[o>>2]|0)|0]|0)==1){if((ue(c[j>>2]|0,c[k>>2]|0,c[o>>2]|0,2)|0)!=0){Q=ve(c[j>>2]|0,c[k>>2]|0,c[y>>2]|0,2)|0;c[(c[z>>2]|0)+4>>2]=Q;qh(c[v>>2]|0,c[z>>2]|0)|0}if((ue(c[j>>2]|0,c[k>>2]|0,c[o>>2]|0,0)|0)!=0){Q=ve(c[j>>2]|0,c[k>>2]|0,c[y>>2]|0,0)|0;c[c[z>>2]>>2]=Q;qh(c[u>>2]|0,c[z>>2]|0)|0}}c[o>>2]=(c[o>>2]|0)+1}a:while(1){c[C>>2]=oh(c[u>>2]|0)|0;c[D>>2]=oh(c[v>>2]|0)|0;if((c[C>>2]|0)==0?(c[D>>2]|0)==0:0){R=54;break}if((c[C>>2]|0)==0){R=16;break}if((c[D>>2]|0)==0){R=16;break}z=(jh(c[l>>2]|0,2)|0)!=0;c[A>>2]=z?0:2;if((c[A>>2]|0)==0){c[B>>2]=c[u>>2]}else{c[B>>2]=c[v>>2]}if((c[m>>2]|0)!=0){c[G>>2]=0;c[I>>2]=0;c[E>>2]=0;while(1){z=sh(c[B>>2]|0,c[E>>2]|0)|0;c[s>>2]=z;if((z|0)==0){break}if((c[s>>2]|0)==0){R=24;break a}c[F>>2]=((c[s>>2]|0)-(c[r>>2]|0)|0)/12|0;if((a[(c[k>>2]|0)+(c[F>>2]|0)|0]|0)!=1){R=26;break a}a[(c[k>>2]|0)+(c[F>>2]|0)|0]=c[A>>2];c[H>>2]=Mb[c[m>>2]&31](c[n>>2]|0,c[k>>2]|0,c[F>>2]|0)|0;a[(c[k>>2]|0)+(c[F>>2]|0)|0]=1;Mb[c[m>>2]&31](c[n>>2]|0,c[k>>2]|0,c[F>>2]|0)|0;if(!((c[G>>2]|0)!=0?(c[H>>2]|0)<=(c[I>>2]|0):0)){c[I>>2]=c[H>>2];c[G>>2]=c[s>>2]}c[E>>2]=(c[E>>2]|0)+1}c[s>>2]=c[G>>2]}else{c[s>>2]=sh(c[B>>2]|0,0)|0}if((c[s>>2]|0)==0){R=34;break}c[o>>2]=((c[s>>2]|0)-(c[r>>2]|0)|0)/12|0;if((a[(c[k>>2]|0)+(c[o>>2]|0)|0]|0)!=1){R=36;break}a[(c[k>>2]|0)+(c[o>>2]|0)|0]=c[A>>2];if((c[m>>2]|0)!=0){Mb[c[m>>2]&31](c[n>>2]|0,c[k>>2]|0,c[o>>2]|0)|0}wh(c[u>>2]|0,c[s>>2]|0)|0;wh(c[v>>2]|0,c[s>>2]|0)|0;c[t>>2]=(c[(c[j>>2]|0)+4>>2]|0)+((c[o>>2]|0)*24|0);c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[c[t>>2]>>2]|0)){continue a}c[J>>2]=c[(c[(c[t>>2]|0)+8>>2]|0)+(c[o>>2]<<2)>>2];c[p>>2]=0;while(1){if((c[p>>2]|0)>=(c[c[J>>2]>>2]|0)){break}c[K>>2]=c[(c[(c[J>>2]|0)+8>>2]|0)+(c[p>>2]<<2)>>2];if((c[K>>2]|0)!=0?(c[K>>2]|0)!=(c[t>>2]|0):0){if((c[K>>2]|0)==0){S=2}else{S=a[(c[k>>2]|0)+(((c[K>>2]|0)-(c[(c[j>>2]|0)+4>>2]|0)|0)/24|0)|0]|0}if((S|0)==1){c[L>>2]=((c[K>>2]|0)-(c[(c[j>>2]|0)+4>>2]|0)|0)/24|0;c[s>>2]=(c[r>>2]|0)+((c[L>>2]|0)*12|0);wh(c[u>>2]|0,c[s>>2]|0)|0;if((ue(c[j>>2]|0,c[k>>2]|0,c[L>>2]|0,0)|0)!=0){z=ve(c[j>>2]|0,c[k>>2]|0,c[K>>2]|0,0)|0;c[c[s>>2]>>2]=z;qh(c[u>>2]|0,c[s>>2]|0)|0}wh(c[v>>2]|0,c[s>>2]|0)|0;if((ue(c[j>>2]|0,c[k>>2]|0,c[L>>2]|0,2)|0)!=0){z=ve(c[j>>2]|0,c[k>>2]|0,c[K>>2]|0,2)|0;c[(c[s>>2]|0)+4>>2]=z;qh(c[v>>2]|0,c[s>>2]|0)|0}}}c[p>>2]=(c[p>>2]|0)+1}c[o>>2]=(c[o>>2]|0)+1}}if((R|0)==16){Ca(1768,1808,374,1824)}else if((R|0)==24){Ca(1840,1808,399,1824)}else if((R|0)==26){Ca(1848,1808,401,1824)}else if((R|0)==34){Ca(1840,1808,416,1824)}else if((R|0)==36){Ca(1872,1808,418,1824)}else if((R|0)==54){mh(c[u>>2]|0);mh(c[v>>2]|0);$f(c[r>>2]|0);c[w>>2]=_f(c[q>>2]<<2)|0;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[q>>2]|0)){break}c[(c[w>>2]|0)+(c[o>>2]<<2)>>2]=c[o>>2];c[o>>2]=(c[o>>2]|0)+1}Mg(c[w>>2]|0,c[q>>2]|0,4,c[l>>2]|0);c[x>>2]=0;while(1){c[M>>2]=0;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[q>>2]|0)){break}c[N>>2]=c[(c[w>>2]|0)+(c[o>>2]<<2)>>2];c[O>>2]=(a[(c[k>>2]|0)+(c[N>>2]|0)|0]|0)==0?2:0;do{if((ue(c[j>>2]|0,c[k>>2]|0,c[N>>2]|0,c[O>>2]|0)|0)!=0){c[P>>2]=(c[(c[j>>2]|0)+4>>2]|0)+((c[N>>2]|0)*24|0);if((c[x>>2]|0)!=0){if((jh(c[l>>2]|0,10)|0)!=0){break}a[(c[k>>2]|0)+(c[N>>2]|0)|0]=c[O>>2];break}else{if((we(c[j>>2]|0,c[k>>2]|0,c[P>>2]|0,c[O>>2]|0)|0)!=1){break}a[(c[k>>2]|0)+(c[N>>2]|0)|0]=c[O>>2];c[M>>2]=1;break}}}while(0);c[o>>2]=(c[o>>2]|0)+1}if((c[x>>2]|0)!=0){break}if((c[M>>2]|0)!=0){continue}c[x>>2]=1}$f(c[w>>2]|0);i=h;return}}function se(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;b=xe(c[e>>2]|0,c[f>>2]|0,0)|0;i=d;return b|0}function te(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;b=xe(c[e>>2]|0,c[f>>2]|0,4)|0;i=d;return b|0}function ue(b,d,e,f){b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0;g=i;i=i+80|0;h=g+64|0;j=g+60|0;k=g+56|0;l=g+52|0;m=g+48|0;n=g+44|0;o=g+40|0;p=g+36|0;q=g+32|0;r=g+28|0;s=g+24|0;t=g+20|0;u=g+16|0;v=g+12|0;w=g+8|0;x=g+4|0;y=g;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[p>>2]=(c[(c[j>>2]|0)+4>>2]|0)+((c[l>>2]|0)*24|0);c[w>>2]=0;if((a[(c[k>>2]|0)+(c[l>>2]|0)|0]|0)==(c[m>>2]|0)){Ca(1896,1808,88,1928)}c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[c[p>>2]>>2]|0)){break}c[x>>2]=c[(c[(c[p>>2]|0)+4>>2]|0)+(c[n>>2]<<2)>>2];l=c[x>>2]|0;if((c[(c[x>>2]|0)+8>>2]|0)==(c[p>>2]|0)){z=c[l+12>>2]|0}else{z=c[l+8>>2]|0}c[y>>2]=z;if((c[y>>2]|0)==0){A=2}else{A=a[(c[k>>2]|0)+(((c[y>>2]|0)-(c[(c[j>>2]|0)+4>>2]|0)|0)/24|0)|0]|0}if((A|0)==(c[m>>2]|0)){B=11;break}c[n>>2]=(c[n>>2]|0)+1}if((B|0)==11){c[w>>2]=1}if((c[w>>2]|0)==0){c[h>>2]=0;C=c[h>>2]|0;i=g;return C|0}c[o>>2]=0;c[n>>2]=0;c[r>>2]=c[c[(c[c[(c[p>>2]|0)+8>>2]>>2]|0)+8>>2]>>2];if((c[r>>2]|0)==(c[p>>2]|0)){c[o>>2]=1;c[r>>2]=c[(c[(c[c[(c[p>>2]|0)+8>>2]>>2]|0)+8>>2]|0)+4>>2]}c[t>>2]=0;if((c[r>>2]|0)==0){D=2}else{D=a[(c[k>>2]|0)+(((c[r>>2]|0)-(c[(c[j>>2]|0)+4>>2]|0)|0)/24|0)|0]|0}c[u>>2]=(D|0)==(c[m>>2]|0);c[s>>2]=0;c[q>>2]=0;while(1){c[o>>2]=(c[o>>2]|0)+1;if((c[o>>2]|0)==(c[c[(c[(c[p>>2]|0)+8>>2]|0)+(c[n>>2]<<2)>>2]>>2]|0)){c[o>>2]=0}if((c[(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+(c[n>>2]<<2)>>2]|0)+8>>2]|0)+(c[o>>2]<<2)>>2]|0)==(c[p>>2]|0)){D=(c[n>>2]|0)+1|0;c[n>>2]=D;c[n>>2]=(c[n>>2]|0)==(c[c[p>>2]>>2]|0)?0:D;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[c[(c[(c[p>>2]|0)+8>>2]|0)+(c[n>>2]<<2)>>2]>>2]|0)){break}if((c[(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+(c[n>>2]<<2)>>2]|0)+8>>2]|0)+(c[o>>2]<<2)>>2]|0)==(c[r>>2]|0)){break}c[o>>2]=(c[o>>2]|0)+1}if((c[o>>2]|0)==(c[c[(c[(c[p>>2]|0)+8>>2]|0)+(c[n>>2]<<2)>>2]>>2]|0)){B=28;break}continue}c[r>>2]=c[(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+(c[n>>2]<<2)>>2]|0)+8>>2]|0)+(c[o>>2]<<2)>>2];if((c[r>>2]|0)==0){E=2}else{E=a[(c[k>>2]|0)+(((c[r>>2]|0)-(c[(c[j>>2]|0)+4>>2]|0)|0)/24|0)|0]|0}c[v>>2]=(E|0)==(c[m>>2]|0);if((c[s>>2]|0)==0){c[s>>2]=c[(c[(c[p>>2]|0)+8>>2]|0)+(c[n>>2]<<2)>>2];c[q>>2]=c[r>>2];c[u>>2]=c[v>>2];continue}if((c[v>>2]|0)!=(c[u>>2]|0)?(c[t>>2]=(c[t>>2]|0)+1,c[u>>2]=c[v>>2],(c[t>>2]|0)>2):0){break}if((c[(c[(c[p>>2]|0)+8>>2]|0)+(c[n>>2]<<2)>>2]|0)!=(c[s>>2]|0)){continue}if((c[r>>2]|0)==(c[q>>2]|0)){break}}if((B|0)==28){Ca(1944,1808,183,1928)}c[h>>2]=(c[t>>2]|0)==2?1:0;C=c[h>>2]|0;i=g;return C|0}function ve(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0;f=i;i=i+16|0;g=f+12|0;h=f+8|0;j=f+4|0;k=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;e=0-(we(c[g>>2]|0,c[h>>2]|0,c[j>>2]|0,c[k>>2]|0)|0)|0;i=f;return e|0}function we(b,d,e,f){b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;g=i;i=i+32|0;h=g+28|0;j=g+24|0;k=g+20|0;l=g+16|0;m=g+12|0;n=g+8|0;o=g+4|0;p=g;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=f;c[m>>2]=0;c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[c[k>>2]>>2]|0)){break}c[p>>2]=c[(c[(c[k>>2]|0)+4>>2]|0)+(c[n>>2]<<2)>>2];f=c[p>>2]|0;if((c[(c[p>>2]|0)+8>>2]|0)==(c[k>>2]|0)){q=c[f+12>>2]|0}else{q=c[f+8>>2]|0}c[o>>2]=q;if((c[o>>2]|0)==0){r=2}else{r=a[(c[j>>2]|0)+(((c[o>>2]|0)-(c[(c[h>>2]|0)+4>>2]|0)|0)/24|0)|0]|0}if((r|0)==(c[l>>2]|0)){c[m>>2]=(c[m>>2]|0)+1}c[n>>2]=(c[n>>2]|0)+1}i=g;return c[m>>2]|0}function xe(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;e=i;i=i+32|0;f=e+24|0;g=e+20|0;h=e+16|0;j=e+12|0;k=e+8|0;l=e+4|0;m=e;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=c[g>>2];c[l>>2]=c[h>>2];c[m>>2]=(c[(c[l>>2]|0)+(c[j>>2]|0)>>2]|0)-(c[(c[k>>2]|0)+(c[j>>2]|0)>>2]|0);if((c[m>>2]|0)!=0){c[f>>2]=c[m>>2];n=c[f>>2]|0;i=e;return n|0}if((c[(c[k>>2]|0)+8>>2]|0)>>>0<(c[(c[l>>2]|0)+8>>2]|0)>>>0){c[f>>2]=-1;n=c[f>>2]|0;i=e;return n|0}if((c[(c[k>>2]|0)+8>>2]|0)>>>0>(c[(c[l>>2]|0)+8>>2]|0)>>>0){c[f>>2]=1;n=c[f>>2]|0;i=e;return n|0}else{c[f>>2]=((c[k>>2]|0)-(c[l>>2]|0)|0)/12|0;n=c[f>>2]|0;i=e;return n|0}return 0}function ye(){var a=0,b=0;a=i;i=i+16|0;b=a;c[b>>2]=_f(16)|0;c[(c[b>>2]|0)+4>>2]=7;c[c[b>>2]>>2]=7;c[(c[b>>2]|0)+8>>2]=0;c[(c[b>>2]|0)+12>>2]=0;i=a;return c[b>>2]|0}function ze(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;e=i;i=i+128|0;f=e;g=e+32|0;h=e+28|0;j=e+24|0;k=e+20|0;l=e+16|0;m=e+40|0;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;if((c[h>>2]|0)<0|(c[h>>2]|0)>>>0>=18){c[g>>2]=0;n=c[g>>2]|0;i=e;return n|0}else{c[l>>2]=_f(16)|0;d=c[l>>2]|0;b=4288+(c[h>>2]<<4)|0;c[d+0>>2]=c[b+0>>2];c[d+4>>2]=c[b+4>>2];c[d+8>>2]=c[b+8>>2];c[d+12>>2]=c[b+12>>2];c[c[k>>2]>>2]=c[l>>2];k=c[c[l>>2]>>2]|0;b=c[4592+(c[(c[l>>2]|0)+12>>2]<<2)>>2]|0;d=c[4648+(c[(c[l>>2]|0)+8>>2]<<2)>>2]|0;c[f>>2]=c[(c[l>>2]|0)+4>>2];c[f+4>>2]=k;c[f+8>>2]=b;c[f+12>>2]=d;cb(m|0,4576,f|0)|0;f=bg(m)|0;c[c[j>>2]>>2]=f;c[g>>2]=1;n=c[g>>2]|0;i=e;return n|0}return 0}function Ae(b,e){b=b|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0;f=i;i=i+16|0;g=f+8|0;h=f+4|0;j=f;c[g>>2]=b;c[h>>2]=e;e=Kh(c[h>>2]|0)|0;c[c[g>>2]>>2]=e;c[(c[g>>2]|0)+4>>2]=e;c[(c[g>>2]|0)+8>>2]=0;while(1){if((a[c[h>>2]|0]|0)!=0){k=(tb(d[c[h>>2]|0]|0)|0)!=0}else{k=0}l=c[h>>2]|0;if(!k){break}c[h>>2]=l+1}a:do{if((a[l]|0)==120){c[h>>2]=(c[h>>2]|0)+1;k=Kh(c[h>>2]|0)|0;c[(c[g>>2]|0)+4>>2]=k;while(1){if((a[c[h>>2]|0]|0)==0){break a}if((tb(d[c[h>>2]|0]|0)|0)==0){break a}c[h>>2]=(c[h>>2]|0)+1}}}while(0);b:do{if((a[c[h>>2]|0]|0)==116){c[h>>2]=(c[h>>2]|0)+1;l=Kh(c[h>>2]|0)|0;c[(c[g>>2]|0)+12>>2]=l;while(1){if((a[c[h>>2]|0]|0)==0){break b}if((tb(d[c[h>>2]|0]|0)|0)==0){break b}c[h>>2]=(c[h>>2]|0)+1}}}while(0);if((a[c[h>>2]|0]|0)!=100){i=f;return}c[h>>2]=(c[h>>2]|0)+1;c[j>>2]=0;while(1){m=a[c[h>>2]|0]|0;if((c[j>>2]|0)>=4){break}if((m<<24>>24|0)==(a[4280+(c[j>>2]|0)|0]|0)){c[(c[g>>2]|0)+8>>2]=c[j>>2]}c[j>>2]=(c[j>>2]|0)+1}if(!(m<<24>>24!=0)){i=f;return}c[h>>2]=(c[h>>2]|0)+1;i=f;return}function Be(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0;e=i;i=i+112|0;f=e;g=e+16|0;h=e+12|0;j=e+24|0;c[g>>2]=b;c[h>>2]=d;d=c[(c[g>>2]|0)+4>>2]|0;b=c[(c[g>>2]|0)+12>>2]|0;c[f>>2]=c[c[g>>2]>>2];c[f+4>>2]=d;c[f+8>>2]=b;cb(j|0,4256,f|0)|0;if((c[h>>2]|0)==0){k=bg(j)|0;i=e;return k|0}h=j+(Nh(j|0)|0)|0;c[f>>2]=a[4280+(c[(c[g>>2]|0)+8>>2]|0)|0]|0;cb(h|0,4272,f|0)|0;k=bg(j)|0;i=e;return k|0}function Ce(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;$f(c[d>>2]|0);i=b;return}function De(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;c[e>>2]=_f(16)|0;a=c[e>>2]|0;f=c[d>>2]|0;c[a+0>>2]=c[f+0>>2];c[a+4>>2]=c[f+4>>2];c[a+8>>2]=c[f+8>>2];c[a+12>>2]=c[f+12>>2];i=b;return c[e>>2]|0}function Ee(a){a=a|0;var b=0,d=0,e=0,f=0,g=0;b=i;i=i+96|0;d=b;e=b+8|0;f=b+4|0;g=b+16|0;c[e>>2]=a;c[f>>2]=_f(80)|0;c[c[f>>2]>>2]=4016;c[(c[f>>2]|0)+4>>2]=0;c[d>>2]=c[c[e>>2]>>2];cb(g|0,2200,d|0)|0;a=bg(g)|0;c[(c[f>>2]|0)+8>>2]=a;c[(c[f>>2]|0)+12>>2]=0;c[(c[f>>2]|0)+16>>2]=4024;c[(c[f>>2]|0)+20>>2]=0;c[d>>2]=c[(c[e>>2]|0)+4>>2];cb(g|0,2200,d|0)|0;d=bg(g)|0;c[(c[f>>2]|0)+24>>2]=d;c[(c[f>>2]|0)+28>>2]=0;c[(c[f>>2]|0)+32>>2]=4032;c[(c[f>>2]|0)+36>>2]=1;c[(c[f>>2]|0)+40>>2]=4048;c[(c[f>>2]|0)+44>>2]=c[(c[e>>2]|0)+12>>2];c[(c[f>>2]|0)+48>>2]=4208;c[(c[f>>2]|0)+52>>2]=1;c[(c[f>>2]|0)+56>>2]=4224;c[(c[f>>2]|0)+60>>2]=c[(c[e>>2]|0)+8>>2];c[(c[f>>2]|0)+64>>2]=0;c[(c[f>>2]|0)+68>>2]=3;c[(c[f>>2]|0)+72>>2]=0;c[(c[f>>2]|0)+76>>2]=0;i=b;return c[f>>2]|0}function Fe(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;c[e>>2]=_f(16)|0;a=Kh(c[(c[d>>2]|0)+8>>2]|0)|0;c[c[e>>2]>>2]=a;a=Kh(c[(c[d>>2]|0)+24>>2]|0)|0;c[(c[e>>2]|0)+4>>2]=a;c[(c[e>>2]|0)+12>>2]=c[(c[d>>2]|0)+44>>2];c[(c[e>>2]|0)+8>>2]=c[(c[d>>2]|0)+60>>2];i=b;return c[e>>2]|0}function Ge(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;c[f>>2]=a;c[d>>2]=b;if((c[(c[f>>2]|0)+12>>2]|0)>=0?!((c[(c[f>>2]|0)+12>>2]|0)>>>0>=13):0){if((c[c[f>>2]>>2]|0)>=(c[3360+(c[(c[f>>2]|0)+12>>2]<<4)>>2]|0)?(c[(c[f>>2]|0)+4>>2]|0)>=(c[3360+(c[(c[f>>2]|0)+12>>2]<<4)>>2]|0):0){if((c[c[f>>2]>>2]|0)<(c[3364+(c[(c[f>>2]|0)+12>>2]<<4)>>2]|0)?(c[(c[f>>2]|0)+4>>2]|0)<(c[3364+(c[(c[f>>2]|0)+12>>2]<<4)>>2]|0):0){c[e>>2]=c[3372+(c[(c[f>>2]|0)+12>>2]<<4)>>2];g=c[e>>2]|0;i=d;return g|0}if((c[(c[f>>2]|0)+8>>2]|0)>=4){Ca(3568,2368,652,3592)}c[e>>2]=0;g=c[e>>2]|0;i=d;return g|0}c[e>>2]=c[3368+(c[(c[f>>2]|0)+12>>2]<<4)>>2];g=c[e>>2]|0;i=d;return g|0}c[e>>2]=3336;g=c[e>>2]|0;i=d;return g|0}function He(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0;f=i;i=i+64|0;g=f;h=f+48|0;j=f+44|0;k=f+32|0;l=f+28|0;m=f+24|0;n=f+20|0;o=f+16|0;p=f+12|0;c[h>>2]=a;c[j>>2]=b;c[f+40>>2]=d;c[f+36>>2]=e;c[o>>2]=_f(28)|0;c[m>>2]=Jc(c[2264+(c[(c[h>>2]|0)+12>>2]<<2)>>2]|0,c[c[h>>2]>>2]|0,c[(c[h>>2]|0)+4>>2]|0,c[j>>2]|0)|0;e=Vf(c[h>>2]|0,c[m>>2]|0)|0;c[n>>2]=e;c[c[o>>2]>>2]=e;e=_f(c[c[n>>2]>>2]|0)|0;c[(c[o>>2]|0)+4>>2]=e;e=_f(c[(c[n>>2]|0)+8>>2]|0)|0;c[(c[o>>2]|0)+8>>2]=e;e=_f(c[(c[n>>2]|0)+8>>2]|0)|0;c[(c[o>>2]|0)+12>>2]=e;c[(c[o>>2]|0)+24>>2]=c[(c[h>>2]|0)+12>>2];do{Oh(c[(c[o>>2]|0)+8>>2]|0,1,c[(c[n>>2]|0)+8>>2]|0)|0;Oh(c[(c[o>>2]|0)+12>>2]|0,0,c[(c[n>>2]|0)+8>>2]|0)|0;c[(c[o>>2]|0)+20>>2]=0;c[(c[o>>2]|0)+16>>2]=0;do{Wf(c[o>>2]|0,c[j>>2]|0)}while((Xf(c[o>>2]|0,c[(c[h>>2]|0)+8>>2]|0)|0)!=0^1);c[p>>2]=Yf(c[o>>2]|0,c[j>>2]|0,c[(c[h>>2]|0)+8>>2]|0)|0;Le(c[o>>2]|0);c[o>>2]=c[p>>2];if((c[(c[h>>2]|0)+8>>2]|0)<=0){break}}while((Xf(c[o>>2]|0,(c[(c[h>>2]|0)+8>>2]|0)-1|0)|0)!=0);c[l>>2]=Zf(c[o>>2]|0)|0;Le(c[o>>2]|0);if((c[m>>2]|0)!=0){o=(Nh(c[m>>2]|0)|0)+1|0;c[k>>2]=_f(o+(Nh(c[l>>2]|0)|0)+1|0)|0;o=c[k>>2]|0;p=c[l>>2]|0;c[g>>2]=c[m>>2];c[g+4>>2]=95;c[g+8>>2]=p;cb(o|0,3152,g|0)|0;$f(c[m>>2]|0);$f(c[l>>2]|0)}else{c[k>>2]=c[l>>2]}if((Ie(c[h>>2]|0,c[k>>2]|0)|0)!=0){Ca(3160,2368,1425,3192)}else{i=f;return c[k>>2]|0}return 0}function Ie(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;e=i;i=i+32|0;f=e+24|0;g=e+20|0;h=e+16|0;j=e+12|0;k=e+8|0;l=e+4|0;m=e;c[g>>2]=b;c[h>>2]=d;c[j>>2]=0;c[l>>2]=Uf(h)|0;c[m>>2]=Lc(c[2264+(c[(c[g>>2]|0)+12>>2]<<2)>>2]|0,c[c[g>>2]>>2]|0,c[(c[g>>2]|0)+4>>2]|0,c[l>>2]|0)|0;if((c[m>>2]|0)!=0){c[f>>2]=c[m>>2];n=c[f>>2]|0;i=e;return n|0}c[k>>2]=Vf(c[g>>2]|0,c[l>>2]|0)|0;if((c[l>>2]|0)!=0){$f(c[l>>2]|0)}a:while(1){if((a[c[h>>2]|0]|0)==0){break}if((a[c[h>>2]|0]|0)>=48?(a[c[h>>2]|0]|0)<=57:0){o=10}else{o=8}do{if((o|0)==8){o=0;if((a[c[h>>2]|0]|0)>=65?(a[c[h>>2]|0]|0)<=90:0){o=10;break}if((a[c[h>>2]|0]|0)<97){o=13;break a}c[j>>2]=(c[j>>2]|0)+((a[c[h>>2]|0]|0)-97+1)}}while(0);if((o|0)==10){o=0;c[j>>2]=(c[j>>2]|0)+1}c[h>>2]=(c[h>>2]|0)+1}if((o|0)==13){c[f>>2]=3032;n=c[f>>2]|0;i=e;return n|0}if((c[j>>2]|0)<(c[c[k>>2]>>2]|0)){c[f>>2]=3072;n=c[f>>2]|0;i=e;return n|0}if((c[j>>2]|0)>(c[c[k>>2]>>2]|0)){c[f>>2]=3112;n=c[f>>2]|0;i=e;return n|0}else{Dc(c[k>>2]|0);c[f>>2]=0;n=c[f>>2]|0;i=e;return n|0}return 0}function Je(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;f=i;i=i+64|0;g=f+44|0;h=f+40|0;j=f+36|0;k=f+32|0;l=f+28|0;m=f+24|0;n=f+20|0;o=f+16|0;p=f+12|0;q=f+8|0;r=f+4|0;s=f;c[f+48>>2]=b;c[g>>2]=d;c[h>>2]=e;c[k>>2]=_f(28)|0;c[l>>2]=0;c[p>>2]=Uf(h)|0;e=Vf(c[g>>2]|0,c[p>>2]|0)|0;c[q>>2]=e;c[c[k>>2]>>2]=e;if((c[p>>2]|0)!=0){$f(c[p>>2]|0)}c[o>>2]=c[h>>2];c[r>>2]=c[c[q>>2]>>2];c[s>>2]=c[(c[q>>2]|0)+8>>2];q=_f(c[r>>2]|0)|0;c[(c[k>>2]|0)+4>>2]=q;q=_f(c[s>>2]|0)|0;c[(c[k>>2]|0)+8>>2]=q;q=_f(c[s>>2]|0)|0;c[(c[k>>2]|0)+12>>2]=q;c[(c[k>>2]|0)+20>>2]=0;c[(c[k>>2]|0)+16>>2]=0;c[(c[k>>2]|0)+24>>2]=c[(c[g>>2]|0)+12>>2];c[j>>2]=0;a:while(1){if((c[j>>2]|0)>=(c[r>>2]|0)){t=18;break}if((c[l>>2]|0)!=0){c[l>>2]=(c[l>>2]|0)+ -1;a[(c[(c[k>>2]|0)+4>>2]|0)+(c[j>>2]|0)|0]=-1}else{if((a[c[o>>2]|0]|0)==0){t=8;break}c[m>>2]=(a[c[o>>2]|0]|0)-48;c[n>>2]=(a[c[o>>2]|0]|0)-65+10;do{if((c[m>>2]|0)>=0&(c[m>>2]|0)<10){a[(c[(c[k>>2]|0)+4>>2]|0)+(c[j>>2]|0)|0]=c[m>>2]}else{if((c[n>>2]|0)>=10&(c[n>>2]|0)<36){a[(c[(c[k>>2]|0)+4>>2]|0)+(c[j>>2]|0)|0]=c[n>>2];break}c[m>>2]=(a[c[o>>2]|0]|0)-97+1;if((c[m>>2]|0)<=0){t=14;break a}a[(c[(c[k>>2]|0)+4>>2]|0)+(c[j>>2]|0)|0]=-1;c[l>>2]=(c[m>>2]|0)-1}}while(0);c[o>>2]=(c[o>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+1}if((t|0)==8){Ca(3e3,2368,1466,3008)}else if((t|0)==14){Ca(3024,2368,1475,3008)}else if((t|0)==18){Oh(c[(c[k>>2]|0)+8>>2]|0,1,c[s>>2]|0)|0;Oh(c[(c[k>>2]|0)+12>>2]|0,0,c[s>>2]|0)|0;i=f;return c[k>>2]|0}return 0}function Ke(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;c[e>>2]=_f(28)|0;c[c[e>>2]>>2]=c[c[d>>2]>>2];a=(c[c[e>>2]>>2]|0)+44|0;c[a>>2]=(c[a>>2]|0)+1;c[(c[e>>2]|0)+16>>2]=c[(c[d>>2]|0)+16>>2];c[(c[e>>2]|0)+20>>2]=c[(c[d>>2]|0)+20>>2];a=_f(c[c[c[d>>2]>>2]>>2]|0)|0;c[(c[e>>2]|0)+4>>2]=a;Qh(c[(c[e>>2]|0)+4>>2]|0,c[(c[d>>2]|0)+4>>2]|0,c[c[c[d>>2]>>2]>>2]|0)|0;a=_f(c[(c[c[d>>2]>>2]|0)+8>>2]|0)|0;c[(c[e>>2]|0)+8>>2]=a;Qh(c[(c[e>>2]|0)+8>>2]|0,c[(c[d>>2]|0)+8>>2]|0,c[(c[c[d>>2]>>2]|0)+8>>2]|0)|0;a=_f(c[(c[c[d>>2]>>2]|0)+8>>2]|0)|0;c[(c[e>>2]|0)+12>>2]=a;Qh(c[(c[e>>2]|0)+12>>2]|0,c[(c[d>>2]|0)+12>>2]|0,c[(c[c[d>>2]>>2]|0)+8>>2]|0)|0;c[(c[e>>2]|0)+24>>2]=c[(c[d>>2]|0)+24>>2];i=b;return c[e>>2]|0}function Le(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[d>>2]|0)==0){i=b;return}Dc(c[c[d>>2]>>2]|0);$f(c[(c[d>>2]|0)+4>>2]|0);$f(c[(c[d>>2]|0)+8>>2]|0);$f(c[(c[d>>2]|0)+12>>2]|0);$f(c[d>>2]|0);i=b;return}function Me(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;f=i;i=i+32|0;g=f+24|0;h=f+8|0;j=f+4|0;k=f;c[g>>2]=a;c[f+20>>2]=b;c[f+16>>2]=d;c[f+12>>2]=e;c[h>>2]=0;c[j>>2]=uf(c[g>>2]|0,4)|0;c[k>>2]=vf(c[j>>2]|0)|0;if((c[(c[k>>2]|0)+4>>2]|0)==0){c[h>>2]=wf(c[c[k>>2]>>2]|0)|0;l=c[k>>2]|0;xf(l);m=c[j>>2]|0;xf(m);n=c[h>>2]|0;i=f;return n|0}else{c[h>>2]=wf(c[c[k>>2]>>2]|0)|0;l=c[k>>2]|0;xf(l);m=c[j>>2]|0;xf(m);n=c[h>>2]|0;i=f;return n|0}return 0}function Ne(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[e>>2]=a;if((c[(c[e>>2]|0)+12>>2]|0)!=0){c[d>>2]=0}else{c[d>>2]=1}i=b;return c[d>>2]|0}



function uh(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0;e=i;i=i+16|0;f=e+8|0;g=e+4|0;h=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;d=th(c[f>>2]|0,c[g>>2]|0,c[h>>2]|0,0,0)|0;i=e;return d|0}function vh(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0;d=i;i=i+32|0;e=d+28|0;f=d+24|0;g=d+20|0;h=d+16|0;j=d+12|0;k=d+8|0;l=d+4|0;m=d;c[e>>2]=a;c[f>>2]=b;c[h>>2]=0;c[g>>2]=c[c[e>>2]>>2];a:while(1){do{if((c[f>>2]|0)<=(c[(c[g>>2]|0)+20>>2]|0)){c[j>>2]=0}else{c[f>>2]=(c[f>>2]|0)-((c[(c[g>>2]|0)+20>>2]|0)+1);if((c[f>>2]|0)<=(c[(c[g>>2]|0)+24>>2]|0)){c[j>>2]=1;break}c[f>>2]=(c[f>>2]|0)-((c[(c[g>>2]|0)+24>>2]|0)+1);if((c[f>>2]|0)<=(c[(c[g>>2]|0)+28>>2]|0)){c[j>>2]=2;break}c[f>>2]=(c[f>>2]|0)-((c[(c[g>>2]|0)+28>>2]|0)+1);if((c[f>>2]|0)>(c[(c[g>>2]|0)+32>>2]|0)){n=10;break a}c[j>>2]=3}}while(0);if((c[(c[g>>2]|0)+4>>2]|0)==0){n=32;break}if((c[f>>2]|0)==(c[(c[g>>2]|0)+20+(c[j>>2]<<2)>>2]|0)){if((c[(c[g>>2]|0)+36+(c[j>>2]<<2)>>2]|0)==0){n=14;break}c[j>>2]=(c[j>>2]|0)+1;c[f>>2]=0;c[m>>2]=c[(c[g>>2]|0)+4+(c[j>>2]<<2)>>2];while(1){if((c[(c[m>>2]|0)+4>>2]|0)==0){break}c[m>>2]=c[(c[m>>2]|0)+4>>2]}c[h>>2]=c[(c[g>>2]|0)+36+((c[j>>2]|0)-1<<2)>>2];c[(c[g>>2]|0)+36+((c[j>>2]|0)-1<<2)>>2]=c[(c[m>>2]|0)+36>>2]}c[l>>2]=c[(c[g>>2]|0)+4+(c[j>>2]<<2)>>2];do{if((c[(c[l>>2]|0)+40>>2]|0)==0){if((c[j>>2]|0)>0?(c[(c[(c[g>>2]|0)+4+((c[j>>2]|0)-1<<2)>>2]|0)+40>>2]|0)!=0:0){yh(c[g>>2]|0,(c[j>>2]|0)-1|0,j,f);break}if(((c[j>>2]|0)<3?(c[(c[g>>2]|0)+4+((c[j>>2]|0)+1<<2)>>2]|0)!=0:0)?(c[(c[(c[g>>2]|0)+4+((c[j>>2]|0)+1<<2)>>2]|0)+40>>2]|0)!=0:0){xh(c[g>>2]|0,(c[j>>2]|0)+1|0,j,f);break}b=c[j>>2]|0;zh(c[g>>2]|0,(c[j>>2]|0)>0?b-1|0:b,j,f);c[l>>2]=c[(c[g>>2]|0)+4+(c[j>>2]<<2)>>2];if((c[(c[g>>2]|0)+36>>2]|0)==0){c[c[e>>2]>>2]=c[l>>2];c[c[l>>2]>>2]=0;$f(c[g>>2]|0);c[g>>2]=0}}}while(0);if((c[g>>2]|0)!=0){b=(c[g>>2]|0)+20+(c[j>>2]<<2)|0;c[b>>2]=(c[b>>2]|0)+ -1}c[g>>2]=c[l>>2]}if((n|0)==10){Ca(5920,5824,900,5928)}else if((n|0)==14){Ca(5952,5824,916,5928)}else if((n|0)==32){if((c[(c[g>>2]|0)+4>>2]|0)!=0){Ca(5968,5824,980,5928)}if((c[h>>2]|0)==0){c[h>>2]=c[(c[g>>2]|0)+36+(c[j>>2]<<2)>>2]}c[k>>2]=c[j>>2];while(1){if((c[k>>2]|0)<2){o=(c[(c[g>>2]|0)+36+((c[k>>2]|0)+1<<2)>>2]|0)!=0}else{o=0}p=c[k>>2]|0;if(!o){break}c[(c[g>>2]|0)+36+(c[k>>2]<<2)>>2]=c[(c[g>>2]|0)+36+(p+1<<2)>>2];c[k>>2]=(c[k>>2]|0)+1}c[(c[g>>2]|0)+36+(p<<2)>>2]=0;if((c[(c[g>>2]|0)+36>>2]|0)!=0){q=c[h>>2]|0;i=d;return q|0}if((c[g>>2]|0)!=(c[c[e>>2]>>2]|0)){Ca(5984,5824,995,5928)}$f(c[g>>2]|0);c[c[e>>2]>>2]=0;q=c[h>>2]|0;i=d;return q|0}return 0}function wh(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0;d=i;i=i+16|0;e=d+12|0;f=d+8|0;g=d+4|0;h=d;c[f>>2]=a;c[g>>2]=b;if((th(c[f>>2]|0,c[g>>2]|0,0,0,h)|0)!=0){c[e>>2]=vh(c[f>>2]|0,c[h>>2]|0)|0;j=c[e>>2]|0;i=d;return j|0}else{c[e>>2]=0;j=c[e>>2]|0;i=d;return j|0}return 0}function xh(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0;f=i;i=i+32|0;g=f+28|0;h=f+24|0;j=f+20|0;k=f+16|0;l=f+12|0;m=f+8|0;n=f+4|0;o=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=c[(c[g>>2]|0)+4+(c[h>>2]<<2)>>2];c[m>>2]=c[(c[g>>2]|0)+4+((c[h>>2]|0)-1<<2)>>2];if((c[(c[m>>2]|0)+40>>2]|0)!=0){p=2}else{p=(c[(c[m>>2]|0)+36>>2]|0)!=0?1:0}c[n>>2]=p;c[(c[m>>2]|0)+36+(c[n>>2]<<2)>>2]=c[(c[g>>2]|0)+36+((c[h>>2]|0)-1<<2)>>2];c[(c[g>>2]|0)+36+((c[h>>2]|0)-1<<2)>>2]=c[(c[l>>2]|0)+36>>2];c[(c[m>>2]|0)+4+((c[n>>2]|0)+1<<2)>>2]=c[(c[l>>2]|0)+4>>2];c[(c[m>>2]|0)+20+((c[n>>2]|0)+1<<2)>>2]=c[(c[l>>2]|0)+20>>2];if((c[(c[m>>2]|0)+4+((c[n>>2]|0)+1<<2)>>2]|0)!=0){c[c[(c[m>>2]|0)+4+((c[n>>2]|0)+1<<2)>>2]>>2]=c[m>>2]}c[(c[l>>2]|0)+4>>2]=c[(c[l>>2]|0)+8>>2];c[(c[l>>2]|0)+20>>2]=c[(c[l>>2]|0)+24>>2];c[(c[l>>2]|0)+36>>2]=c[(c[l>>2]|0)+40>>2];c[(c[l>>2]|0)+8>>2]=c[(c[l>>2]|0)+12>>2];c[(c[l>>2]|0)+24>>2]=c[(c[l>>2]|0)+28>>2];c[(c[l>>2]|0)+40>>2]=c[(c[l>>2]|0)+44>>2];c[(c[l>>2]|0)+12>>2]=c[(c[l>>2]|0)+16>>2];c[(c[l>>2]|0)+28>>2]=c[(c[l>>2]|0)+32>>2];c[(c[l>>2]|0)+44>>2]=0;c[(c[l>>2]|0)+16>>2]=0;c[(c[l>>2]|0)+32>>2]=0;c[o>>2]=(c[(c[m>>2]|0)+20+((c[n>>2]|0)+1<<2)>>2]|0)+1;n=(c[g>>2]|0)+20+(c[h>>2]<<2)|0;c[n>>2]=(c[n>>2]|0)-(c[o>>2]|0);n=(c[g>>2]|0)+20+((c[h>>2]|0)-1<<2)|0;c[n>>2]=(c[n>>2]|0)+(c[o>>2]|0);if((c[j>>2]|0)==0){i=f;return}if((c[c[j>>2]>>2]|0)!=(c[h>>2]|0)){i=f;return}n=c[k>>2]|0;c[n>>2]=(c[n>>2]|0)-(c[o>>2]|0);if((c[c[k>>2]>>2]|0)>=0){i=f;return}o=c[k>>2]|0;c[o>>2]=(c[o>>2]|0)+((c[(c[g>>2]|0)+20+((c[h>>2]|0)-1<<2)>>2]|0)+1);h=c[j>>2]|0;c[h>>2]=(c[h>>2]|0)+ -1;i=f;return}function yh(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0;f=i;i=i+48|0;g=f+32|0;h=f+28|0;j=f+24|0;k=f+20|0;l=f+16|0;m=f+12|0;n=f+8|0;o=f+4|0;p=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=c[(c[g>>2]|0)+4+(c[h>>2]<<2)>>2];c[m>>2]=c[(c[g>>2]|0)+4+((c[h>>2]|0)+1<<2)>>2];c[(c[m>>2]|0)+16>>2]=c[(c[m>>2]|0)+12>>2];c[(c[m>>2]|0)+32>>2]=c[(c[m>>2]|0)+28>>2];c[(c[m>>2]|0)+44>>2]=c[(c[m>>2]|0)+40>>2];c[(c[m>>2]|0)+12>>2]=c[(c[m>>2]|0)+8>>2];c[(c[m>>2]|0)+28>>2]=c[(c[m>>2]|0)+24>>2];c[(c[m>>2]|0)+40>>2]=c[(c[m>>2]|0)+36>>2];c[(c[m>>2]|0)+8>>2]=c[(c[m>>2]|0)+4>>2];c[(c[m>>2]|0)+24>>2]=c[(c[m>>2]|0)+20>>2];if((c[(c[l>>2]|0)+44>>2]|0)!=0){q=2}else{q=(c[(c[l>>2]|0)+40>>2]|0)!=0?1:0}c[n>>2]=q;c[(c[m>>2]|0)+36>>2]=c[(c[g>>2]|0)+36+(c[h>>2]<<2)>>2];c[(c[g>>2]|0)+36+(c[h>>2]<<2)>>2]=c[(c[l>>2]|0)+36+(c[n>>2]<<2)>>2];c[(c[l>>2]|0)+36+(c[n>>2]<<2)>>2]=0;c[(c[m>>2]|0)+4>>2]=c[(c[l>>2]|0)+4+((c[n>>2]|0)+1<<2)>>2];c[(c[m>>2]|0)+20>>2]=c[(c[l>>2]|0)+20+((c[n>>2]|0)+1<<2)>>2];c[(c[l>>2]|0)+4+((c[n>>2]|0)+1<<2)>>2]=0;c[(c[l>>2]|0)+20+((c[n>>2]|0)+1<<2)>>2]=0;if((c[(c[m>>2]|0)+4>>2]|0)!=0){c[c[(c[m>>2]|0)+4>>2]>>2]=c[m>>2]}c[p>>2]=(c[(c[m>>2]|0)+20>>2]|0)+1;m=(c[g>>2]|0)+20+(c[h>>2]<<2)|0;c[m>>2]=(c[m>>2]|0)-(c[p>>2]|0);m=(c[g>>2]|0)+20+((c[h>>2]|0)+1<<2)|0;c[m>>2]=(c[m>>2]|0)+(c[p>>2]|0);c[o>>2]=c[(c[g>>2]|0)+20+(c[h>>2]<<2)>>2];if((c[j>>2]|0)==0){i=f;return}if((c[c[j>>2]>>2]|0)==(c[h>>2]|0)?(c[c[k>>2]>>2]|0)>(c[o>>2]|0):0){g=c[k>>2]|0;c[g>>2]=(c[g>>2]|0)-((c[o>>2]|0)+1);o=c[j>>2]|0;c[o>>2]=(c[o>>2]|0)+1;i=f;return}if((c[c[j>>2]>>2]|0)!=((c[h>>2]|0)+1|0)){i=f;return}h=c[k>>2]|0;c[h>>2]=(c[h>>2]|0)+(c[p>>2]|0);i=f;return}function zh(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;f=i;i=i+48|0;g=f+40|0;h=f+36|0;j=f+32|0;k=f+28|0;l=f+24|0;m=f+20|0;n=f+16|0;o=f+12|0;p=f+8|0;q=f+4|0;r=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=c[(c[g>>2]|0)+4+(c[h>>2]<<2)>>2];c[o>>2]=c[(c[g>>2]|0)+20+(c[h>>2]<<2)>>2];c[m>>2]=c[(c[g>>2]|0)+4+((c[h>>2]|0)+1<<2)>>2];c[p>>2]=c[(c[g>>2]|0)+20+((c[h>>2]|0)+1<<2)>>2];if((c[(c[l>>2]|0)+44>>2]|0)!=0){Ca(5856,5824,809,5896)}if((c[(c[m>>2]|0)+44>>2]|0)!=0){Ca(5856,5824,809,5896)}if((c[(c[l>>2]|0)+40>>2]|0)!=0){s=2}else{s=(c[(c[l>>2]|0)+36>>2]|0)!=0?1:0}c[q>>2]=s;if((c[(c[m>>2]|0)+40>>2]|0)!=0){t=2}else{t=(c[(c[m>>2]|0)+36>>2]|0)!=0?1:0}c[r>>2]=t;c[(c[l>>2]|0)+36+(c[q>>2]<<2)>>2]=c[(c[g>>2]|0)+36+(c[h>>2]<<2)>>2];c[n>>2]=0;while(1){if((c[n>>2]|0)>=((c[r>>2]|0)+1|0)){break}c[(c[l>>2]|0)+4+((c[q>>2]|0)+1+(c[n>>2]|0)<<2)>>2]=c[(c[m>>2]|0)+4+(c[n>>2]<<2)>>2];c[(c[l>>2]|0)+20+((c[q>>2]|0)+1+(c[n>>2]|0)<<2)>>2]=c[(c[m>>2]|0)+20+(c[n>>2]<<2)>>2];if((c[(c[l>>2]|0)+4+((c[q>>2]|0)+1+(c[n>>2]|0)<<2)>>2]|0)!=0){c[c[(c[l>>2]|0)+4+((c[q>>2]|0)+1+(c[n>>2]|0)<<2)>>2]>>2]=c[l>>2]}if((c[n>>2]|0)<(c[r>>2]|0)){c[(c[l>>2]|0)+36+((c[q>>2]|0)+1+(c[n>>2]|0)<<2)>>2]=c[(c[m>>2]|0)+36+(c[n>>2]<<2)>>2]}c[n>>2]=(c[n>>2]|0)+1}q=(c[g>>2]|0)+20+(c[h>>2]<<2)|0;c[q>>2]=(c[q>>2]|0)+((c[p>>2]|0)+1);$f(c[m>>2]|0);c[n>>2]=(c[h>>2]|0)+1;while(1){if((c[n>>2]|0)>=3){break}c[(c[g>>2]|0)+4+(c[n>>2]<<2)>>2]=c[(c[g>>2]|0)+4+((c[n>>2]|0)+1<<2)>>2];c[(c[g>>2]|0)+20+(c[n>>2]<<2)>>2]=c[(c[g>>2]|0)+20+((c[n>>2]|0)+1<<2)>>2];c[n>>2]=(c[n>>2]|0)+1}c[n>>2]=c[h>>2];while(1){if((c[n>>2]|0)>=2){break}c[(c[g>>2]|0)+36+(c[n>>2]<<2)>>2]=c[(c[g>>2]|0)+36+((c[n>>2]|0)+1<<2)>>2];c[n>>2]=(c[n>>2]|0)+1}c[(c[g>>2]|0)+16>>2]=0;c[(c[g>>2]|0)+32>>2]=0;c[(c[g>>2]|0)+44>>2]=0;if((c[j>>2]|0)==0){i=f;return}g=c[j>>2]|0;n=c[g>>2]|0;if((c[c[j>>2]>>2]|0)==((c[h>>2]|0)+1|0)){c[g>>2]=n+ -1;g=c[k>>2]|0;c[g>>2]=(c[g>>2]|0)+((c[o>>2]|0)+1);i=f;return}if((n|0)<=((c[h>>2]|0)+1|0)){i=f;return}h=c[j>>2]|0;c[h>>2]=(c[h>>2]|0)+ -1;i=f;return}function Ah(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;h=i;i=i+48|0;j=h+44|0;k=h+40|0;l=h+36|0;m=h+32|0;n=h+28|0;o=h+24|0;p=h+20|0;q=h+16|0;r=h+12|0;s=h+8|0;t=h+4|0;u=h;c[k>>2]=a;c[l>>2]=b;c[m>>2]=d;c[n>>2]=e;c[o>>2]=f;c[p>>2]=g;c[q>>2]=ph(c[k>>2]|0)|0;c[r>>2]=ph(c[m>>2]|0)|0;while(1){if((c[o>>2]|0)==0){break}if((c[(c[o>>2]|0)+40>>2]|0)==0){v=4;break}if((c[(c[o>>2]|0)+44>>2]|0)==0){v=14;break}c[s>>2]=_f(48)|0;c[c[s>>2]>>2]=c[c[o>>2]>>2];do{if((c[p>>2]|0)!=0){if((c[p>>2]|0)==1){c[(c[s>>2]|0)+4>>2]=c[(c[o>>2]|0)+4>>2];c[(c[s>>2]|0)+20>>2]=c[(c[o>>2]|0)+20>>2];c[(c[s>>2]|0)+36>>2]=c[(c[o>>2]|0)+36>>2];c[(c[s>>2]|0)+8>>2]=c[k>>2];c[(c[s>>2]|0)+24>>2]=c[q>>2];c[(c[s>>2]|0)+40>>2]=c[l>>2];c[(c[s>>2]|0)+12>>2]=c[m>>2];c[(c[s>>2]|0)+28>>2]=c[r>>2];c[l>>2]=c[(c[o>>2]|0)+40>>2];c[(c[o>>2]|0)+4>>2]=c[(c[o>>2]|0)+12>>2];c[(c[o>>2]|0)+20>>2]=c[(c[o>>2]|0)+28>>2];c[(c[o>>2]|0)+36>>2]=c[(c[o>>2]|0)+44>>2];c[(c[o>>2]|0)+8>>2]=c[(c[o>>2]|0)+16>>2];c[(c[o>>2]|0)+24>>2]=c[(c[o>>2]|0)+32>>2];break}g=(c[p>>2]|0)==2;c[(c[s>>2]|0)+4>>2]=c[(c[o>>2]|0)+4>>2];c[(c[s>>2]|0)+20>>2]=c[(c[o>>2]|0)+20>>2];c[(c[s>>2]|0)+36>>2]=c[(c[o>>2]|0)+36>>2];c[(c[s>>2]|0)+8>>2]=c[(c[o>>2]|0)+8>>2];c[(c[s>>2]|0)+24>>2]=c[(c[o>>2]|0)+24>>2];c[(c[s>>2]|0)+40>>2]=c[(c[o>>2]|0)+40>>2];if(g){c[(c[s>>2]|0)+12>>2]=c[k>>2];c[(c[s>>2]|0)+28>>2]=c[q>>2];c[(c[o>>2]|0)+4>>2]=c[m>>2];c[(c[o>>2]|0)+20>>2]=c[r>>2];c[(c[o>>2]|0)+36>>2]=c[(c[o>>2]|0)+44>>2];c[(c[o>>2]|0)+8>>2]=c[(c[o>>2]|0)+16>>2];c[(c[o>>2]|0)+24>>2]=c[(c[o>>2]|0)+32>>2];break}else{c[(c[s>>2]|0)+12>>2]=c[(c[o>>2]|0)+12>>2];c[(c[s>>2]|0)+28>>2]=c[(c[o>>2]|0)+28>>2];c[(c[o>>2]|0)+4>>2]=c[k>>2];c[(c[o>>2]|0)+20>>2]=c[q>>2];c[(c[o>>2]|0)+36>>2]=c[l>>2];c[(c[o>>2]|0)+8>>2]=c[m>>2];c[(c[o>>2]|0)+24>>2]=c[r>>2];c[l>>2]=c[(c[o>>2]|0)+44>>2];break}}else{c[(c[s>>2]|0)+4>>2]=c[k>>2];c[(c[s>>2]|0)+20>>2]=c[q>>2];c[(c[s>>2]|0)+36>>2]=c[l>>2];c[(c[s>>2]|0)+8>>2]=c[m>>2];c[(c[s>>2]|0)+24>>2]=c[r>>2];c[(c[s>>2]|0)+40>>2]=c[(c[o>>2]|0)+36>>2];c[(c[s>>2]|0)+12>>2]=c[(c[o>>2]|0)+8>>2];c[(c[s>>2]|0)+28>>2]=c[(c[o>>2]|0)+24>>2];c[l>>2]=c[(c[o>>2]|0)+40>>2];c[(c[o>>2]|0)+4>>2]=c[(c[o>>2]|0)+12>>2];c[(c[o>>2]|0)+20>>2]=c[(c[o>>2]|0)+28>>2];c[(c[o>>2]|0)+36>>2]=c[(c[o>>2]|0)+44>>2];c[(c[o>>2]|0)+8>>2]=c[(c[o>>2]|0)+16>>2];c[(c[o>>2]|0)+24>>2]=c[(c[o>>2]|0)+32>>2]}}while(0);c[(c[o>>2]|0)+12>>2]=0;c[(c[o>>2]|0)+16>>2]=0;c[(c[s>>2]|0)+16>>2]=0;c[(c[o>>2]|0)+28>>2]=0;c[(c[o>>2]|0)+32>>2]=0;c[(c[s>>2]|0)+32>>2]=0;c[(c[o>>2]|0)+40>>2]=0;c[(c[o>>2]|0)+44>>2]=0;c[(c[s>>2]|0)+44>>2]=0;if((c[(c[s>>2]|0)+4>>2]|0)!=0){c[c[(c[s>>2]|0)+4>>2]>>2]=c[s>>2]}if((c[(c[s>>2]|0)+8>>2]|0)!=0){c[c[(c[s>>2]|0)+8>>2]>>2]=c[s>>2]}if((c[(c[s>>2]|0)+12>>2]|0)!=0){c[c[(c[s>>2]|0)+12>>2]>>2]=c[s>>2]}if((c[(c[o>>2]|0)+4>>2]|0)!=0){c[c[(c[o>>2]|0)+4>>2]>>2]=c[o>>2]}if((c[(c[o>>2]|0)+8>>2]|0)!=0){c[c[(c[o>>2]|0)+8>>2]>>2]=c[o>>2]}c[k>>2]=c[s>>2];c[q>>2]=ph(c[k>>2]|0)|0;c[m>>2]=c[o>>2];c[r>>2]=ph(c[m>>2]|0)|0;if((c[c[o>>2]>>2]|0)!=0){if((c[(c[c[o>>2]>>2]|0)+4>>2]|0)!=(c[o>>2]|0)){if((c[(c[c[o>>2]>>2]|0)+8>>2]|0)==(c[o>>2]|0)){w=1}else{w=(c[(c[c[o>>2]>>2]|0)+12>>2]|0)==(c[o>>2]|0)?2:3}}else{w=0}c[p>>2]=w}c[o>>2]=c[c[o>>2]>>2]}if((v|0)==4){if((c[p>>2]|0)==0){c[(c[o>>2]|0)+12>>2]=c[(c[o>>2]|0)+8>>2];c[(c[o>>2]|0)+28>>2]=c[(c[o>>2]|0)+24>>2];c[(c[o>>2]|0)+40>>2]=c[(c[o>>2]|0)+36>>2];c[(c[o>>2]|0)+8>>2]=c[m>>2];c[(c[o>>2]|0)+24>>2]=c[r>>2];c[(c[o>>2]|0)+36>>2]=c[l>>2];c[(c[o>>2]|0)+4>>2]=c[k>>2];c[(c[o>>2]|0)+20>>2]=c[q>>2]}else{c[(c[o>>2]|0)+12>>2]=c[m>>2];c[(c[o>>2]|0)+28>>2]=c[r>>2];c[(c[o>>2]|0)+40>>2]=c[l>>2];c[(c[o>>2]|0)+8>>2]=c[k>>2];c[(c[o>>2]|0)+24>>2]=c[q>>2]}if((c[(c[o>>2]|0)+4>>2]|0)!=0){c[c[(c[o>>2]|0)+4>>2]>>2]=c[o>>2]}if((c[(c[o>>2]|0)+8>>2]|0)!=0){c[c[(c[o>>2]|0)+8>>2]>>2]=c[o>>2]}if((c[(c[o>>2]|0)+12>>2]|0)!=0){c[c[(c[o>>2]|0)+12>>2]>>2]=c[o>>2]}}else if((v|0)==14){do{if((c[p>>2]|0)!=0){if((c[p>>2]|0)==1){c[(c[o>>2]|0)+16>>2]=c[(c[o>>2]|0)+12>>2];c[(c[o>>2]|0)+32>>2]=c[(c[o>>2]|0)+28>>2];c[(c[o>>2]|0)+44>>2]=c[(c[o>>2]|0)+40>>2];c[(c[o>>2]|0)+12>>2]=c[m>>2];c[(c[o>>2]|0)+28>>2]=c[r>>2];c[(c[o>>2]|0)+40>>2]=c[l>>2];c[(c[o>>2]|0)+8>>2]=c[k>>2];c[(c[o>>2]|0)+24>>2]=c[q>>2];break}else{c[(c[o>>2]|0)+16>>2]=c[m>>2];c[(c[o>>2]|0)+32>>2]=c[r>>2];c[(c[o>>2]|0)+44>>2]=c[l>>2];c[(c[o>>2]|0)+12>>2]=c[k>>2];c[(c[o>>2]|0)+28>>2]=c[q>>2];break}}else{c[(c[o>>2]|0)+16>>2]=c[(c[o>>2]|0)+12>>2];c[(c[o>>2]|0)+32>>2]=c[(c[o>>2]|0)+28>>2];c[(c[o>>2]|0)+44>>2]=c[(c[o>>2]|0)+40>>2];c[(c[o>>2]|0)+12>>2]=c[(c[o>>2]|0)+8>>2];c[(c[o>>2]|0)+28>>2]=c[(c[o>>2]|0)+24>>2];c[(c[o>>2]|0)+40>>2]=c[(c[o>>2]|0)+36>>2];c[(c[o>>2]|0)+8>>2]=c[m>>2];c[(c[o>>2]|0)+24>>2]=c[r>>2];c[(c[o>>2]|0)+36>>2]=c[l>>2];c[(c[o>>2]|0)+4>>2]=c[k>>2];c[(c[o>>2]|0)+20>>2]=c[q>>2]}}while(0);if((c[(c[o>>2]|0)+4>>2]|0)!=0){c[c[(c[o>>2]|0)+4>>2]>>2]=c[o>>2]}if((c[(c[o>>2]|0)+8>>2]|0)!=0){c[c[(c[o>>2]|0)+8>>2]>>2]=c[o>>2]}if((c[(c[o>>2]|0)+12>>2]|0)!=0){c[c[(c[o>>2]|0)+12>>2]>>2]=c[o>>2]}if((c[(c[o>>2]|0)+16>>2]|0)!=0){c[c[(c[o>>2]|0)+16>>2]>>2]=c[o>>2]}}if((c[o>>2]|0)==0){p=_f(48)|0;c[c[n>>2]>>2]=p;c[(c[c[n>>2]>>2]|0)+4>>2]=c[k>>2];c[(c[c[n>>2]>>2]|0)+20>>2]=c[q>>2];c[(c[c[n>>2]>>2]|0)+36>>2]=c[l>>2];c[(c[c[n>>2]>>2]|0)+8>>2]=c[m>>2];c[(c[c[n>>2]>>2]|0)+24>>2]=c[r>>2];c[(c[c[n>>2]>>2]|0)+40>>2]=0;c[(c[c[n>>2]>>2]|0)+12>>2]=0;c[(c[c[n>>2]>>2]|0)+28>>2]=0;c[(c[c[n>>2]>>2]|0)+44>>2]=0;c[(c[c[n>>2]>>2]|0)+16>>2]=0;c[(c[c[n>>2]>>2]|0)+32>>2]=0;c[c[c[n>>2]>>2]>>2]=0;if((c[(c[c[n>>2]>>2]|0)+4>>2]|0)!=0){c[c[(c[c[n>>2]>>2]|0)+4>>2]>>2]=c[c[n>>2]>>2]}if((c[(c[c[n>>2]>>2]|0)+8>>2]|0)!=0){c[c[(c[c[n>>2]>>2]|0)+8>>2]>>2]=c[c[n>>2]>>2]}c[j>>2]=1;x=c[j>>2]|0;i=h;return x|0}while(1){if((c[c[o>>2]>>2]|0)==0){break}c[t>>2]=ph(c[o>>2]|0)|0;if((c[(c[c[o>>2]>>2]|0)+4>>2]|0)!=(c[o>>2]|0)){if((c[(c[c[o>>2]>>2]|0)+8>>2]|0)==(c[o>>2]|0)){y=1}else{y=(c[(c[c[o>>2]>>2]|0)+12>>2]|0)==(c[o>>2]|0)?2:3}}else{y=0}c[u>>2]=y;c[(c[c[o>>2]>>2]|0)+20+(c[u>>2]<<2)>>2]=c[t>>2];c[o>>2]=c[c[o>>2]>>2]}c[j>>2]=0;x=c[j>>2]|0;i=h;return x|0}function Bh(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;f=i;g=d&255;h=(e|0)==0;a:do{if((b&3|0)==0|h){j=e;k=h;l=b;m=5}else{n=d&255;o=e;p=b;while(1){if((a[p]|0)==n<<24>>24){q=o;r=p;m=6;break a}s=p+1|0;t=o+ -1|0;u=(t|0)==0;if((s&3|0)==0|u){j=t;k=u;l=s;m=5;break}else{o=t;p=s}}}}while(0);if((m|0)==5){if(k){v=0;w=l}else{q=j;r=l;m=6}}b:do{if((m|0)==6){l=d&255;if(!((a[r]|0)==l<<24>>24)){j=Z(g,16843009)|0;c:do{if(q>>>0>3){k=q;b=r;while(1){e=c[b>>2]^j;if(((e&-2139062144^-2139062144)&e+ -16843009|0)!=0){x=k;y=b;break c}e=b+4|0;h=k+ -4|0;if(h>>>0>3){k=h;b=e}else{x=h;y=e;break}}}else{x=q;y=r}}while(0);if((x|0)==0){v=0;w=y}else{j=x;b=y;while(1){if((a[b]|0)==l<<24>>24){v=j;w=b;break b}k=b+1|0;e=j+ -1|0;if((e|0)==0){v=0;w=k;break}else{j=e;b=k}}}}else{v=q;w=r}}}while(0);i=f;return((v|0)!=0?w:0)|0}function Ch(b,c){b=b|0;c=c|0;var d=0,e=0;d=i;e=Dh(b,c)|0;i=d;return((a[e]|0)==(c&255)<<24>>24?e:0)|0}function Dh(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;e=i;f=d&255;if((f|0)==0){g=b+(Nh(b|0)|0)|0;i=e;return g|0}a:do{if((b&3|0)!=0){h=d&255;j=b;while(1){k=a[j]|0;if(k<<24>>24==0){g=j;l=13;break}m=j+1|0;if(k<<24>>24==h<<24>>24){g=j;l=13;break}if((m&3|0)==0){n=m;break a}else{j=m}}if((l|0)==13){i=e;return g|0}}else{n=b}}while(0);b=Z(f,16843009)|0;f=c[n>>2]|0;b:do{if(((f&-2139062144^-2139062144)&f+ -16843009|0)==0){l=f;j=n;while(1){h=l^b;m=j+4|0;if(((h&-2139062144^-2139062144)&h+ -16843009|0)!=0){o=j;break b}h=c[m>>2]|0;if(((h&-2139062144^-2139062144)&h+ -16843009|0)==0){l=h;j=m}else{o=m;break}}}else{o=n}}while(0);n=d&255;d=o;while(1){o=a[d]|0;if(o<<24>>24==0|o<<24>>24==n<<24>>24){g=d;break}else{d=d+1|0}}i=e;return g|0}function Eh(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0;e=i;i=i+32|0;f=e;c[f+0>>2]=0;c[f+4>>2]=0;c[f+8>>2]=0;c[f+12>>2]=0;c[f+16>>2]=0;c[f+20>>2]=0;c[f+24>>2]=0;c[f+28>>2]=0;g=a[d]|0;if(g<<24>>24==0){h=0;i=e;return h|0}if((a[d+1|0]|0)==0){j=b;while(1){if((a[j]|0)==g<<24>>24){j=j+1|0}else{break}}h=j-b|0;i=e;return h|0}else{k=d;l=g}do{g=l&255;d=f+(g>>>5<<2)|0;c[d>>2]=c[d>>2]|1<<(g&31);k=k+1|0;l=a[k]|0}while(!(l<<24>>24==0));l=a[b]|0;a:do{if(l<<24>>24==0){m=b}else{k=b;g=l;while(1){d=g&255;j=k+1|0;if((c[f+(d>>>5<<2)>>2]&1<<(d&31)|0)==0){m=k;break a}d=a[j]|0;if(d<<24>>24==0){m=j;break}else{k=j;g=d}}}}while(0);h=m-b|0;i=e;return h|0}function Fh(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0,L=0,M=0,N=0,O=0,P=0,Q=0,R=0,S=0,T=0,U=0,V=0,W=0,X=0,Y=0,Z=0,_=0,$=0,aa=0,ba=0,ca=0,da=0,ea=0,fa=0,ga=0,ha=0,ia=0,ja=0,ka=0,la=0,ma=0,na=0,oa=0,pa=0,qa=0,ra=0,sa=0,ta=0,ua=0,va=0,wa=0,xa=0,ya=0,za=0,Aa=0,Ba=0,Ca=0,Da=0,Ea=0,Fa=0,Ga=0,Ha=0,Ia=0,Ja=0,Ka=0;b=i;do{if(a>>>0<245){if(a>>>0<11){d=16}else{d=a+11&-8}e=d>>>3;f=c[1500]|0;g=f>>>e;if((g&3|0)!=0){h=(g&1^1)+e|0;j=h<<1;k=6040+(j<<2)|0;l=6040+(j+2<<2)|0;j=c[l>>2]|0;m=j+8|0;n=c[m>>2]|0;do{if((k|0)!=(n|0)){if(n>>>0<(c[6016>>2]|0)>>>0){pb()}o=n+12|0;if((c[o>>2]|0)==(j|0)){c[o>>2]=k;c[l>>2]=n;break}else{pb()}}else{c[1500]=f&~(1<<h)}}while(0);n=h<<3;c[j+4>>2]=n|3;l=j+(n|4)|0;c[l>>2]=c[l>>2]|1;p=m;i=b;return p|0}if(d>>>0>(c[6008>>2]|0)>>>0){if((g|0)!=0){l=2<<e;n=g<<e&(l|0-l);l=(n&0-n)+ -1|0;n=l>>>12&16;k=l>>>n;l=k>>>5&8;o=k>>>l;k=o>>>2&4;q=o>>>k;o=q>>>1&2;r=q>>>o;q=r>>>1&1;s=(l|n|k|o|q)+(r>>>q)|0;q=s<<1;r=6040+(q<<2)|0;o=6040+(q+2<<2)|0;q=c[o>>2]|0;k=q+8|0;n=c[k>>2]|0;do{if((r|0)!=(n|0)){if(n>>>0<(c[6016>>2]|0)>>>0){pb()}l=n+12|0;if((c[l>>2]|0)==(q|0)){c[l>>2]=r;c[o>>2]=n;break}else{pb()}}else{c[1500]=f&~(1<<s)}}while(0);f=s<<3;n=f-d|0;c[q+4>>2]=d|3;o=q+d|0;c[q+(d|4)>>2]=n|1;c[q+f>>2]=n;f=c[6008>>2]|0;if((f|0)!=0){r=c[6020>>2]|0;e=f>>>3;f=e<<1;g=6040+(f<<2)|0;m=c[1500]|0;j=1<<e;if((m&j|0)!=0){e=6040+(f+2<<2)|0;h=c[e>>2]|0;if(h>>>0<(c[6016>>2]|0)>>>0){pb()}else{t=e;u=h}}else{c[1500]=m|j;t=6040+(f+2<<2)|0;u=g}c[t>>2]=r;c[u+12>>2]=r;c[r+8>>2]=u;c[r+12>>2]=g}c[6008>>2]=n;c[6020>>2]=o;p=k;i=b;return p|0}o=c[6004>>2]|0;if((o|0)!=0){n=(o&0-o)+ -1|0;o=n>>>12&16;g=n>>>o;n=g>>>5&8;r=g>>>n;g=r>>>2&4;f=r>>>g;r=f>>>1&2;j=f>>>r;f=j>>>1&1;m=c[6304+((n|o|g|r|f)+(j>>>f)<<2)>>2]|0;f=(c[m+4>>2]&-8)-d|0;j=m;r=m;while(1){m=c[j+16>>2]|0;if((m|0)==0){g=c[j+20>>2]|0;if((g|0)==0){break}else{v=g}}else{v=m}m=(c[v+4>>2]&-8)-d|0;g=m>>>0<f>>>0;f=g?m:f;j=v;r=g?v:r}j=c[6016>>2]|0;if(r>>>0<j>>>0){pb()}k=r+d|0;if(!(r>>>0<k>>>0)){pb()}q=c[r+24>>2]|0;s=c[r+12>>2]|0;do{if((s|0)==(r|0)){g=r+20|0;m=c[g>>2]|0;if((m|0)==0){o=r+16|0;n=c[o>>2]|0;if((n|0)==0){w=0;break}else{x=n;y=o}}else{x=m;y=g}while(1){g=x+20|0;m=c[g>>2]|0;if((m|0)!=0){x=m;y=g;continue}g=x+16|0;m=c[g>>2]|0;if((m|0)==0){break}else{x=m;y=g}}if(y>>>0<j>>>0){pb()}else{c[y>>2]=0;w=x;break}}else{g=c[r+8>>2]|0;if(g>>>0<j>>>0){pb()}m=g+12|0;if((c[m>>2]|0)!=(r|0)){pb()}o=s+8|0;if((c[o>>2]|0)==(r|0)){c[m>>2]=s;c[o>>2]=g;w=s;break}else{pb()}}}while(0);do{if((q|0)!=0){s=c[r+28>>2]|0;j=6304+(s<<2)|0;if((r|0)==(c[j>>2]|0)){c[j>>2]=w;if((w|0)==0){c[6004>>2]=c[6004>>2]&~(1<<s);break}}else{if(q>>>0<(c[6016>>2]|0)>>>0){pb()}s=q+16|0;if((c[s>>2]|0)==(r|0)){c[s>>2]=w}else{c[q+20>>2]=w}if((w|0)==0){break}}if(w>>>0<(c[6016>>2]|0)>>>0){pb()}c[w+24>>2]=q;s=c[r+16>>2]|0;do{if((s|0)!=0){if(s>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[w+16>>2]=s;c[s+24>>2]=w;break}}}while(0);s=c[r+20>>2]|0;if((s|0)!=0){if(s>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[w+20>>2]=s;c[s+24>>2]=w;break}}}}while(0);if(f>>>0<16){q=f+d|0;c[r+4>>2]=q|3;s=r+(q+4)|0;c[s>>2]=c[s>>2]|1}else{c[r+4>>2]=d|3;c[r+(d|4)>>2]=f|1;c[r+(f+d)>>2]=f;s=c[6008>>2]|0;if((s|0)!=0){q=c[6020>>2]|0;j=s>>>3;s=j<<1;g=6040+(s<<2)|0;o=c[1500]|0;m=1<<j;if((o&m|0)!=0){j=6040+(s+2<<2)|0;n=c[j>>2]|0;if(n>>>0<(c[6016>>2]|0)>>>0){pb()}else{z=j;A=n}}else{c[1500]=o|m;z=6040+(s+2<<2)|0;A=g}c[z>>2]=q;c[A+12>>2]=q;c[q+8>>2]=A;c[q+12>>2]=g}c[6008>>2]=f;c[6020>>2]=k}p=r+8|0;i=b;return p|0}else{B=d}}else{B=d}}else{if(!(a>>>0>4294967231)){g=a+11|0;q=g&-8;s=c[6004>>2]|0;if((s|0)!=0){m=0-q|0;o=g>>>8;if((o|0)!=0){if(q>>>0>16777215){C=31}else{g=(o+1048320|0)>>>16&8;n=o<<g;o=(n+520192|0)>>>16&4;j=n<<o;n=(j+245760|0)>>>16&2;h=14-(o|g|n)+(j<<n>>>15)|0;C=q>>>(h+7|0)&1|h<<1}}else{C=0}h=c[6304+(C<<2)>>2]|0;a:do{if((h|0)==0){D=m;E=0;F=0}else{if((C|0)==31){G=0}else{G=25-(C>>>1)|0}n=m;j=0;g=q<<G;o=h;e=0;while(1){l=c[o+4>>2]&-8;H=l-q|0;if(H>>>0<n>>>0){if((l|0)==(q|0)){D=H;E=o;F=o;break a}else{I=H;J=o}}else{I=n;J=e}H=c[o+20>>2]|0;l=c[o+(g>>>31<<2)+16>>2]|0;K=(H|0)==0|(H|0)==(l|0)?j:H;if((l|0)==0){D=I;E=K;F=J;break}else{n=I;j=K;g=g<<1;o=l;e=J}}}}while(0);if((E|0)==0&(F|0)==0){h=2<<C;m=s&(h|0-h);if((m|0)==0){B=q;break}h=(m&0-m)+ -1|0;m=h>>>12&16;r=h>>>m;h=r>>>5&8;k=r>>>h;r=k>>>2&4;f=k>>>r;k=f>>>1&2;e=f>>>k;f=e>>>1&1;L=c[6304+((h|m|r|k|f)+(e>>>f)<<2)>>2]|0}else{L=E}if((L|0)==0){M=D;N=F}else{f=D;e=L;k=F;while(1){r=(c[e+4>>2]&-8)-q|0;m=r>>>0<f>>>0;h=m?r:f;r=m?e:k;m=c[e+16>>2]|0;if((m|0)!=0){f=h;e=m;k=r;continue}m=c[e+20>>2]|0;if((m|0)==0){M=h;N=r;break}else{f=h;e=m;k=r}}}if((N|0)!=0?M>>>0<((c[6008>>2]|0)-q|0)>>>0:0){k=c[6016>>2]|0;if(N>>>0<k>>>0){pb()}e=N+q|0;if(!(N>>>0<e>>>0)){pb()}f=c[N+24>>2]|0;s=c[N+12>>2]|0;do{if((s|0)==(N|0)){r=N+20|0;m=c[r>>2]|0;if((m|0)==0){h=N+16|0;o=c[h>>2]|0;if((o|0)==0){O=0;break}else{P=o;Q=h}}else{P=m;Q=r}while(1){r=P+20|0;m=c[r>>2]|0;if((m|0)!=0){P=m;Q=r;continue}r=P+16|0;m=c[r>>2]|0;if((m|0)==0){break}else{P=m;Q=r}}if(Q>>>0<k>>>0){pb()}else{c[Q>>2]=0;O=P;break}}else{r=c[N+8>>2]|0;if(r>>>0<k>>>0){pb()}m=r+12|0;if((c[m>>2]|0)!=(N|0)){pb()}h=s+8|0;if((c[h>>2]|0)==(N|0)){c[m>>2]=s;c[h>>2]=r;O=s;break}else{pb()}}}while(0);do{if((f|0)!=0){s=c[N+28>>2]|0;k=6304+(s<<2)|0;if((N|0)==(c[k>>2]|0)){c[k>>2]=O;if((O|0)==0){c[6004>>2]=c[6004>>2]&~(1<<s);break}}else{if(f>>>0<(c[6016>>2]|0)>>>0){pb()}s=f+16|0;if((c[s>>2]|0)==(N|0)){c[s>>2]=O}else{c[f+20>>2]=O}if((O|0)==0){break}}if(O>>>0<(c[6016>>2]|0)>>>0){pb()}c[O+24>>2]=f;s=c[N+16>>2]|0;do{if((s|0)!=0){if(s>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[O+16>>2]=s;c[s+24>>2]=O;break}}}while(0);s=c[N+20>>2]|0;if((s|0)!=0){if(s>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[O+20>>2]=s;c[s+24>>2]=O;break}}}}while(0);b:do{if(!(M>>>0<16)){c[N+4>>2]=q|3;c[N+(q|4)>>2]=M|1;c[N+(M+q)>>2]=M;f=M>>>3;if(M>>>0<256){s=f<<1;k=6040+(s<<2)|0;r=c[1500]|0;h=1<<f;if((r&h|0)!=0){f=6040+(s+2<<2)|0;m=c[f>>2]|0;if(m>>>0<(c[6016>>2]|0)>>>0){pb()}else{R=f;S=m}}else{c[1500]=r|h;R=6040+(s+2<<2)|0;S=k}c[R>>2]=e;c[S+12>>2]=e;c[N+(q+8)>>2]=S;c[N+(q+12)>>2]=k;break}k=M>>>8;if((k|0)!=0){if(M>>>0>16777215){T=31}else{s=(k+1048320|0)>>>16&8;h=k<<s;k=(h+520192|0)>>>16&4;r=h<<k;h=(r+245760|0)>>>16&2;m=14-(k|s|h)+(r<<h>>>15)|0;T=M>>>(m+7|0)&1|m<<1}}else{T=0}m=6304+(T<<2)|0;c[N+(q+28)>>2]=T;c[N+(q+20)>>2]=0;c[N+(q+16)>>2]=0;h=c[6004>>2]|0;r=1<<T;if((h&r|0)==0){c[6004>>2]=h|r;c[m>>2]=e;c[N+(q+24)>>2]=m;c[N+(q+12)>>2]=e;c[N+(q+8)>>2]=e;break}r=c[m>>2]|0;if((T|0)==31){U=0}else{U=25-(T>>>1)|0}c:do{if((c[r+4>>2]&-8|0)!=(M|0)){m=M<<U;h=r;while(1){V=h+(m>>>31<<2)+16|0;s=c[V>>2]|0;if((s|0)==0){break}if((c[s+4>>2]&-8|0)==(M|0)){W=s;break c}else{m=m<<1;h=s}}if(V>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[V>>2]=e;c[N+(q+24)>>2]=h;c[N+(q+12)>>2]=e;c[N+(q+8)>>2]=e;break b}}else{W=r}}while(0);r=W+8|0;m=c[r>>2]|0;s=c[6016>>2]|0;if(W>>>0<s>>>0){pb()}if(m>>>0<s>>>0){pb()}else{c[m+12>>2]=e;c[r>>2]=e;c[N+(q+8)>>2]=m;c[N+(q+12)>>2]=W;c[N+(q+24)>>2]=0;break}}else{m=M+q|0;c[N+4>>2]=m|3;r=N+(m+4)|0;c[r>>2]=c[r>>2]|1}}while(0);p=N+8|0;i=b;return p|0}else{B=q}}else{B=q}}else{B=-1}}}while(0);N=c[6008>>2]|0;if(!(B>>>0>N>>>0)){M=N-B|0;W=c[6020>>2]|0;if(M>>>0>15){c[6020>>2]=W+B;c[6008>>2]=M;c[W+(B+4)>>2]=M|1;c[W+N>>2]=M;c[W+4>>2]=B|3}else{c[6008>>2]=0;c[6020>>2]=0;c[W+4>>2]=N|3;M=W+(N+4)|0;c[M>>2]=c[M>>2]|1}p=W+8|0;i=b;return p|0}W=c[6012>>2]|0;if(B>>>0<W>>>0){M=W-B|0;c[6012>>2]=M;W=c[6024>>2]|0;c[6024>>2]=W+B;c[W+(B+4)>>2]=M|1;c[W+4>>2]=B|3;p=W+8|0;i=b;return p|0}do{if((c[1618]|0)==0){W=Ta(30)|0;if((W+ -1&W|0)==0){c[6480>>2]=W;c[6476>>2]=W;c[6484>>2]=-1;c[6488>>2]=-1;c[6492>>2]=0;c[6444>>2]=0;c[1618]=(sb(0)|0)&-16^1431655768;break}else{pb()}}}while(0);W=B+48|0;M=c[6480>>2]|0;N=B+47|0;V=M+N|0;U=0-M|0;M=V&U;if(!(M>>>0>B>>>0)){p=0;i=b;return p|0}T=c[6440>>2]|0;if((T|0)!=0?(S=c[6432>>2]|0,R=S+M|0,R>>>0<=S>>>0|R>>>0>T>>>0):0){p=0;i=b;return p|0}d:do{if((c[6444>>2]&4|0)==0){T=c[6024>>2]|0;e:do{if((T|0)!=0){R=6448|0;while(1){S=c[R>>2]|0;if(!(S>>>0>T>>>0)?(X=R+4|0,(S+(c[X>>2]|0)|0)>>>0>T>>>0):0){break}S=c[R+8>>2]|0;if((S|0)==0){Y=182;break e}else{R=S}}if((R|0)!=0){S=V-(c[6012>>2]|0)&U;if(S>>>0<2147483647){O=La(S|0)|0;P=(O|0)==((c[R>>2]|0)+(c[X>>2]|0)|0);Z=O;_=S;$=P?O:-1;aa=P?S:0;Y=191}else{ba=0}}else{Y=182}}else{Y=182}}while(0);do{if((Y|0)==182){T=La(0)|0;if((T|0)!=(-1|0)){q=T;S=c[6476>>2]|0;P=S+ -1|0;if((P&q|0)==0){ca=M}else{ca=M-q+(P+q&0-S)|0}S=c[6432>>2]|0;q=S+ca|0;if(ca>>>0>B>>>0&ca>>>0<2147483647){P=c[6440>>2]|0;if((P|0)!=0?q>>>0<=S>>>0|q>>>0>P>>>0:0){ba=0;break}P=La(ca|0)|0;q=(P|0)==(T|0);Z=P;_=ca;$=q?T:-1;aa=q?ca:0;Y=191}else{ba=0}}else{ba=0}}}while(0);f:do{if((Y|0)==191){q=0-_|0;if(($|0)!=(-1|0)){da=$;ea=aa;Y=202;break d}do{if((Z|0)!=(-1|0)&_>>>0<2147483647&_>>>0<W>>>0?(T=c[6480>>2]|0,P=N-_+T&0-T,P>>>0<2147483647):0){if((La(P|0)|0)==(-1|0)){La(q|0)|0;ba=aa;break f}else{fa=P+_|0;break}}else{fa=_}}while(0);if((Z|0)==(-1|0)){ba=aa}else{da=Z;ea=fa;Y=202;break d}}}while(0);c[6444>>2]=c[6444>>2]|4;ga=ba;Y=199}else{ga=0;Y=199}}while(0);if((((Y|0)==199?M>>>0<2147483647:0)?(ba=La(M|0)|0,M=La(0)|0,(M|0)!=(-1|0)&(ba|0)!=(-1|0)&ba>>>0<M>>>0):0)?(fa=M-ba|0,M=fa>>>0>(B+40|0)>>>0,M):0){da=ba;ea=M?fa:ga;Y=202}if((Y|0)==202){ga=(c[6432>>2]|0)+ea|0;c[6432>>2]=ga;if(ga>>>0>(c[6436>>2]|0)>>>0){c[6436>>2]=ga}ga=c[6024>>2]|0;g:do{if((ga|0)!=0){fa=6448|0;while(1){ha=c[fa>>2]|0;ia=fa+4|0;ja=c[ia>>2]|0;if((da|0)==(ha+ja|0)){Y=214;break}M=c[fa+8>>2]|0;if((M|0)==0){break}else{fa=M}}if(((Y|0)==214?(c[fa+12>>2]&8|0)==0:0)?ga>>>0>=ha>>>0&ga>>>0<da>>>0:0){c[ia>>2]=ja+ea;M=(c[6012>>2]|0)+ea|0;ba=ga+8|0;if((ba&7|0)==0){ka=0}else{ka=0-ba&7}ba=M-ka|0;c[6024>>2]=ga+ka;c[6012>>2]=ba;c[ga+(ka+4)>>2]=ba|1;c[ga+(M+4)>>2]=40;c[6028>>2]=c[6488>>2];break}if(da>>>0<(c[6016>>2]|0)>>>0){c[6016>>2]=da}M=da+ea|0;ba=6448|0;while(1){if((c[ba>>2]|0)==(M|0)){Y=224;break}Z=c[ba+8>>2]|0;if((Z|0)==0){break}else{ba=Z}}if((Y|0)==224?(c[ba+12>>2]&8|0)==0:0){c[ba>>2]=da;M=ba+4|0;c[M>>2]=(c[M>>2]|0)+ea;M=da+8|0;if((M&7|0)==0){la=0}else{la=0-M&7}M=da+(ea+8)|0;if((M&7|0)==0){ma=0}else{ma=0-M&7}M=da+(ma+ea)|0;fa=la+B|0;Z=da+fa|0;aa=M-(da+la)-B|0;c[da+(la+4)>>2]=B|3;h:do{if((M|0)!=(c[6024>>2]|0)){if((M|0)==(c[6020>>2]|0)){_=(c[6008>>2]|0)+aa|0;c[6008>>2]=_;c[6020>>2]=Z;c[da+(fa+4)>>2]=_|1;c[da+(_+fa)>>2]=_;break}_=ea+4|0;N=c[da+(_+ma)>>2]|0;if((N&3|0)==1){W=N&-8;$=N>>>3;do{if(!(N>>>0<256)){ca=c[da+((ma|24)+ea)>>2]|0;X=c[da+(ea+12+ma)>>2]|0;do{if((X|0)==(M|0)){U=ma|16;V=da+(_+U)|0;q=c[V>>2]|0;if((q|0)==0){R=da+(U+ea)|0;U=c[R>>2]|0;if((U|0)==0){na=0;break}else{oa=U;pa=R}}else{oa=q;pa=V}while(1){V=oa+20|0;q=c[V>>2]|0;if((q|0)!=0){oa=q;pa=V;continue}V=oa+16|0;q=c[V>>2]|0;if((q|0)==0){break}else{oa=q;pa=V}}if(pa>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[pa>>2]=0;na=oa;break}}else{V=c[da+((ma|8)+ea)>>2]|0;if(V>>>0<(c[6016>>2]|0)>>>0){pb()}q=V+12|0;if((c[q>>2]|0)!=(M|0)){pb()}R=X+8|0;if((c[R>>2]|0)==(M|0)){c[q>>2]=X;c[R>>2]=V;na=X;break}else{pb()}}}while(0);if((ca|0)!=0){X=c[da+(ea+28+ma)>>2]|0;h=6304+(X<<2)|0;if((M|0)==(c[h>>2]|0)){c[h>>2]=na;if((na|0)==0){c[6004>>2]=c[6004>>2]&~(1<<X);break}}else{if(ca>>>0<(c[6016>>2]|0)>>>0){pb()}X=ca+16|0;if((c[X>>2]|0)==(M|0)){c[X>>2]=na}else{c[ca+20>>2]=na}if((na|0)==0){break}}if(na>>>0<(c[6016>>2]|0)>>>0){pb()}c[na+24>>2]=ca;X=ma|16;h=c[da+(X+ea)>>2]|0;do{if((h|0)!=0){if(h>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[na+16>>2]=h;c[h+24>>2]=na;break}}}while(0);h=c[da+(_+X)>>2]|0;if((h|0)!=0){if(h>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[na+20>>2]=h;c[h+24>>2]=na;break}}}}else{h=c[da+((ma|8)+ea)>>2]|0;ca=c[da+(ea+12+ma)>>2]|0;V=6040+($<<1<<2)|0;if((h|0)!=(V|0)){if(h>>>0<(c[6016>>2]|0)>>>0){pb()}if((c[h+12>>2]|0)!=(M|0)){pb()}}if((ca|0)==(h|0)){c[1500]=c[1500]&~(1<<$);break}if((ca|0)!=(V|0)){if(ca>>>0<(c[6016>>2]|0)>>>0){pb()}V=ca+8|0;if((c[V>>2]|0)==(M|0)){qa=V}else{pb()}}else{qa=ca+8|0}c[h+12>>2]=ca;c[qa>>2]=h}}while(0);ra=da+((W|ma)+ea)|0;sa=W+aa|0}else{ra=M;sa=aa}$=ra+4|0;c[$>>2]=c[$>>2]&-2;c[da+(fa+4)>>2]=sa|1;c[da+(sa+fa)>>2]=sa;$=sa>>>3;if(sa>>>0<256){_=$<<1;N=6040+(_<<2)|0;h=c[1500]|0;ca=1<<$;if((h&ca|0)!=0){$=6040+(_+2<<2)|0;V=c[$>>2]|0;if(V>>>0<(c[6016>>2]|0)>>>0){pb()}else{ta=$;ua=V}}else{c[1500]=h|ca;ta=6040+(_+2<<2)|0;ua=N}c[ta>>2]=Z;c[ua+12>>2]=Z;c[da+(fa+8)>>2]=ua;c[da+(fa+12)>>2]=N;break}N=sa>>>8;if((N|0)!=0){if(sa>>>0>16777215){va=31}else{_=(N+1048320|0)>>>16&8;ca=N<<_;N=(ca+520192|0)>>>16&4;h=ca<<N;ca=(h+245760|0)>>>16&2;V=14-(N|_|ca)+(h<<ca>>>15)|0;va=sa>>>(V+7|0)&1|V<<1}}else{va=0}V=6304+(va<<2)|0;c[da+(fa+28)>>2]=va;c[da+(fa+20)>>2]=0;c[da+(fa+16)>>2]=0;ca=c[6004>>2]|0;h=1<<va;if((ca&h|0)==0){c[6004>>2]=ca|h;c[V>>2]=Z;c[da+(fa+24)>>2]=V;c[da+(fa+12)>>2]=Z;c[da+(fa+8)>>2]=Z;break}h=c[V>>2]|0;if((va|0)==31){wa=0}else{wa=25-(va>>>1)|0}i:do{if((c[h+4>>2]&-8|0)!=(sa|0)){V=sa<<wa;ca=h;while(1){xa=ca+(V>>>31<<2)+16|0;_=c[xa>>2]|0;if((_|0)==0){break}if((c[_+4>>2]&-8|0)==(sa|0)){ya=_;break i}else{V=V<<1;ca=_}}if(xa>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[xa>>2]=Z;c[da+(fa+24)>>2]=ca;c[da+(fa+12)>>2]=Z;c[da+(fa+8)>>2]=Z;break h}}else{ya=h}}while(0);h=ya+8|0;W=c[h>>2]|0;V=c[6016>>2]|0;if(ya>>>0<V>>>0){pb()}if(W>>>0<V>>>0){pb()}else{c[W+12>>2]=Z;c[h>>2]=Z;c[da+(fa+8)>>2]=W;c[da+(fa+12)>>2]=ya;c[da+(fa+24)>>2]=0;break}}else{W=(c[6012>>2]|0)+aa|0;c[6012>>2]=W;c[6024>>2]=Z;c[da+(fa+4)>>2]=W|1}}while(0);p=da+(la|8)|0;i=b;return p|0}fa=6448|0;while(1){za=c[fa>>2]|0;if(!(za>>>0>ga>>>0)?(Aa=c[fa+4>>2]|0,Ba=za+Aa|0,Ba>>>0>ga>>>0):0){break}fa=c[fa+8>>2]|0}fa=za+(Aa+ -39)|0;if((fa&7|0)==0){Ca=0}else{Ca=0-fa&7}fa=za+(Aa+ -47+Ca)|0;Z=fa>>>0<(ga+16|0)>>>0?ga:fa;fa=Z+8|0;aa=da+8|0;if((aa&7|0)==0){Da=0}else{Da=0-aa&7}aa=ea+ -40-Da|0;c[6024>>2]=da+Da;c[6012>>2]=aa;c[da+(Da+4)>>2]=aa|1;c[da+(ea+ -36)>>2]=40;c[6028>>2]=c[6488>>2];c[Z+4>>2]=27;c[fa+0>>2]=c[6448>>2];c[fa+4>>2]=c[6452>>2];c[fa+8>>2]=c[6456>>2];c[fa+12>>2]=c[6460>>2];c[6448>>2]=da;c[6452>>2]=ea;c[6460>>2]=0;c[6456>>2]=fa;fa=Z+28|0;c[fa>>2]=7;if((Z+32|0)>>>0<Ba>>>0){aa=fa;do{fa=aa;aa=aa+4|0;c[aa>>2]=7}while((fa+8|0)>>>0<Ba>>>0)}if((Z|0)!=(ga|0)){aa=Z-ga|0;fa=ga+(aa+4)|0;c[fa>>2]=c[fa>>2]&-2;c[ga+4>>2]=aa|1;c[ga+aa>>2]=aa;fa=aa>>>3;if(aa>>>0<256){M=fa<<1;ba=6040+(M<<2)|0;W=c[1500]|0;h=1<<fa;if((W&h|0)!=0){fa=6040+(M+2<<2)|0;V=c[fa>>2]|0;if(V>>>0<(c[6016>>2]|0)>>>0){pb()}else{Ea=fa;Fa=V}}else{c[1500]=W|h;Ea=6040+(M+2<<2)|0;Fa=ba}c[Ea>>2]=ga;c[Fa+12>>2]=ga;c[ga+8>>2]=Fa;c[ga+12>>2]=ba;break}ba=aa>>>8;if((ba|0)!=0){if(aa>>>0>16777215){Ga=31}else{M=(ba+1048320|0)>>>16&8;h=ba<<M;ba=(h+520192|0)>>>16&4;W=h<<ba;h=(W+245760|0)>>>16&2;V=14-(ba|M|h)+(W<<h>>>15)|0;Ga=aa>>>(V+7|0)&1|V<<1}}else{Ga=0}V=6304+(Ga<<2)|0;c[ga+28>>2]=Ga;c[ga+20>>2]=0;c[ga+16>>2]=0;h=c[6004>>2]|0;W=1<<Ga;if((h&W|0)==0){c[6004>>2]=h|W;c[V>>2]=ga;c[ga+24>>2]=V;c[ga+12>>2]=ga;c[ga+8>>2]=ga;break}W=c[V>>2]|0;if((Ga|0)==31){Ha=0}else{Ha=25-(Ga>>>1)|0}j:do{if((c[W+4>>2]&-8|0)!=(aa|0)){V=aa<<Ha;h=W;while(1){Ia=h+(V>>>31<<2)+16|0;M=c[Ia>>2]|0;if((M|0)==0){break}if((c[M+4>>2]&-8|0)==(aa|0)){Ja=M;break j}else{V=V<<1;h=M}}if(Ia>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[Ia>>2]=ga;c[ga+24>>2]=h;c[ga+12>>2]=ga;c[ga+8>>2]=ga;break g}}else{Ja=W}}while(0);W=Ja+8|0;aa=c[W>>2]|0;Z=c[6016>>2]|0;if(Ja>>>0<Z>>>0){pb()}if(aa>>>0<Z>>>0){pb()}else{c[aa+12>>2]=ga;c[W>>2]=ga;c[ga+8>>2]=aa;c[ga+12>>2]=Ja;c[ga+24>>2]=0;break}}}else{aa=c[6016>>2]|0;if((aa|0)==0|da>>>0<aa>>>0){c[6016>>2]=da}c[6448>>2]=da;c[6452>>2]=ea;c[6460>>2]=0;c[6036>>2]=c[1618];c[6032>>2]=-1;aa=0;do{W=aa<<1;Z=6040+(W<<2)|0;c[6040+(W+3<<2)>>2]=Z;c[6040+(W+2<<2)>>2]=Z;aa=aa+1|0}while((aa|0)!=32);aa=da+8|0;if((aa&7|0)==0){Ka=0}else{Ka=0-aa&7}aa=ea+ -40-Ka|0;c[6024>>2]=da+Ka;c[6012>>2]=aa;c[da+(Ka+4)>>2]=aa|1;c[da+(ea+ -36)>>2]=40;c[6028>>2]=c[6488>>2]}}while(0);ea=c[6012>>2]|0;if(ea>>>0>B>>>0){da=ea-B|0;c[6012>>2]=da;ea=c[6024>>2]|0;c[6024>>2]=ea+B;c[ea+(B+4)>>2]=da|1;c[ea+4>>2]=B|3;p=ea+8|0;i=b;return p|0}}c[(Pa()|0)>>2]=12;p=0;i=b;return p|0}function Gh(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0;b=i;if((a|0)==0){i=b;return}d=a+ -8|0;e=c[6016>>2]|0;if(d>>>0<e>>>0){pb()}f=c[a+ -4>>2]|0;g=f&3;if((g|0)==1){pb()}h=f&-8;j=a+(h+ -8)|0;do{if((f&1|0)==0){k=c[d>>2]|0;if((g|0)==0){i=b;return}l=-8-k|0;m=a+l|0;n=k+h|0;if(m>>>0<e>>>0){pb()}if((m|0)==(c[6020>>2]|0)){o=a+(h+ -4)|0;if((c[o>>2]&3|0)!=3){p=m;q=n;break}c[6008>>2]=n;c[o>>2]=c[o>>2]&-2;c[a+(l+4)>>2]=n|1;c[j>>2]=n;i=b;return}o=k>>>3;if(k>>>0<256){k=c[a+(l+8)>>2]|0;r=c[a+(l+12)>>2]|0;s=6040+(o<<1<<2)|0;if((k|0)!=(s|0)){if(k>>>0<e>>>0){pb()}if((c[k+12>>2]|0)!=(m|0)){pb()}}if((r|0)==(k|0)){c[1500]=c[1500]&~(1<<o);p=m;q=n;break}if((r|0)!=(s|0)){if(r>>>0<e>>>0){pb()}s=r+8|0;if((c[s>>2]|0)==(m|0)){t=s}else{pb()}}else{t=r+8|0}c[k+12>>2]=r;c[t>>2]=k;p=m;q=n;break}k=c[a+(l+24)>>2]|0;r=c[a+(l+12)>>2]|0;do{if((r|0)==(m|0)){s=a+(l+20)|0;o=c[s>>2]|0;if((o|0)==0){u=a+(l+16)|0;v=c[u>>2]|0;if((v|0)==0){w=0;break}else{x=v;y=u}}else{x=o;y=s}while(1){s=x+20|0;o=c[s>>2]|0;if((o|0)!=0){x=o;y=s;continue}s=x+16|0;o=c[s>>2]|0;if((o|0)==0){break}else{x=o;y=s}}if(y>>>0<e>>>0){pb()}else{c[y>>2]=0;w=x;break}}else{s=c[a+(l+8)>>2]|0;if(s>>>0<e>>>0){pb()}o=s+12|0;if((c[o>>2]|0)!=(m|0)){pb()}u=r+8|0;if((c[u>>2]|0)==(m|0)){c[o>>2]=r;c[u>>2]=s;w=r;break}else{pb()}}}while(0);if((k|0)!=0){r=c[a+(l+28)>>2]|0;s=6304+(r<<2)|0;if((m|0)==(c[s>>2]|0)){c[s>>2]=w;if((w|0)==0){c[6004>>2]=c[6004>>2]&~(1<<r);p=m;q=n;break}}else{if(k>>>0<(c[6016>>2]|0)>>>0){pb()}r=k+16|0;if((c[r>>2]|0)==(m|0)){c[r>>2]=w}else{c[k+20>>2]=w}if((w|0)==0){p=m;q=n;break}}if(w>>>0<(c[6016>>2]|0)>>>0){pb()}c[w+24>>2]=k;r=c[a+(l+16)>>2]|0;do{if((r|0)!=0){if(r>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[w+16>>2]=r;c[r+24>>2]=w;break}}}while(0);r=c[a+(l+20)>>2]|0;if((r|0)!=0){if(r>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[w+20>>2]=r;c[r+24>>2]=w;p=m;q=n;break}}else{p=m;q=n}}else{p=m;q=n}}else{p=d;q=h}}while(0);if(!(p>>>0<j>>>0)){pb()}d=a+(h+ -4)|0;w=c[d>>2]|0;if((w&1|0)==0){pb()}if((w&2|0)==0){if((j|0)==(c[6024>>2]|0)){e=(c[6012>>2]|0)+q|0;c[6012>>2]=e;c[6024>>2]=p;c[p+4>>2]=e|1;if((p|0)!=(c[6020>>2]|0)){i=b;return}c[6020>>2]=0;c[6008>>2]=0;i=b;return}if((j|0)==(c[6020>>2]|0)){e=(c[6008>>2]|0)+q|0;c[6008>>2]=e;c[6020>>2]=p;c[p+4>>2]=e|1;c[p+e>>2]=e;i=b;return}e=(w&-8)+q|0;x=w>>>3;do{if(!(w>>>0<256)){y=c[a+(h+16)>>2]|0;t=c[a+(h|4)>>2]|0;do{if((t|0)==(j|0)){g=a+(h+12)|0;f=c[g>>2]|0;if((f|0)==0){r=a+(h+8)|0;k=c[r>>2]|0;if((k|0)==0){z=0;break}else{A=k;B=r}}else{A=f;B=g}while(1){g=A+20|0;f=c[g>>2]|0;if((f|0)!=0){A=f;B=g;continue}g=A+16|0;f=c[g>>2]|0;if((f|0)==0){break}else{A=f;B=g}}if(B>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[B>>2]=0;z=A;break}}else{g=c[a+h>>2]|0;if(g>>>0<(c[6016>>2]|0)>>>0){pb()}f=g+12|0;if((c[f>>2]|0)!=(j|0)){pb()}r=t+8|0;if((c[r>>2]|0)==(j|0)){c[f>>2]=t;c[r>>2]=g;z=t;break}else{pb()}}}while(0);if((y|0)!=0){t=c[a+(h+20)>>2]|0;n=6304+(t<<2)|0;if((j|0)==(c[n>>2]|0)){c[n>>2]=z;if((z|0)==0){c[6004>>2]=c[6004>>2]&~(1<<t);break}}else{if(y>>>0<(c[6016>>2]|0)>>>0){pb()}t=y+16|0;if((c[t>>2]|0)==(j|0)){c[t>>2]=z}else{c[y+20>>2]=z}if((z|0)==0){break}}if(z>>>0<(c[6016>>2]|0)>>>0){pb()}c[z+24>>2]=y;t=c[a+(h+8)>>2]|0;do{if((t|0)!=0){if(t>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[z+16>>2]=t;c[t+24>>2]=z;break}}}while(0);t=c[a+(h+12)>>2]|0;if((t|0)!=0){if(t>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[z+20>>2]=t;c[t+24>>2]=z;break}}}}else{t=c[a+h>>2]|0;y=c[a+(h|4)>>2]|0;n=6040+(x<<1<<2)|0;if((t|0)!=(n|0)){if(t>>>0<(c[6016>>2]|0)>>>0){pb()}if((c[t+12>>2]|0)!=(j|0)){pb()}}if((y|0)==(t|0)){c[1500]=c[1500]&~(1<<x);break}if((y|0)!=(n|0)){if(y>>>0<(c[6016>>2]|0)>>>0){pb()}n=y+8|0;if((c[n>>2]|0)==(j|0)){C=n}else{pb()}}else{C=y+8|0}c[t+12>>2]=y;c[C>>2]=t}}while(0);c[p+4>>2]=e|1;c[p+e>>2]=e;if((p|0)==(c[6020>>2]|0)){c[6008>>2]=e;i=b;return}else{D=e}}else{c[d>>2]=w&-2;c[p+4>>2]=q|1;c[p+q>>2]=q;D=q}q=D>>>3;if(D>>>0<256){w=q<<1;d=6040+(w<<2)|0;e=c[1500]|0;C=1<<q;if((e&C|0)!=0){q=6040+(w+2<<2)|0;j=c[q>>2]|0;if(j>>>0<(c[6016>>2]|0)>>>0){pb()}else{E=q;F=j}}else{c[1500]=e|C;E=6040+(w+2<<2)|0;F=d}c[E>>2]=p;c[F+12>>2]=p;c[p+8>>2]=F;c[p+12>>2]=d;i=b;return}d=D>>>8;if((d|0)!=0){if(D>>>0>16777215){G=31}else{F=(d+1048320|0)>>>16&8;E=d<<F;d=(E+520192|0)>>>16&4;w=E<<d;E=(w+245760|0)>>>16&2;C=14-(d|F|E)+(w<<E>>>15)|0;G=D>>>(C+7|0)&1|C<<1}}else{G=0}C=6304+(G<<2)|0;c[p+28>>2]=G;c[p+20>>2]=0;c[p+16>>2]=0;E=c[6004>>2]|0;w=1<<G;a:do{if((E&w|0)!=0){F=c[C>>2]|0;if((G|0)==31){H=0}else{H=25-(G>>>1)|0}b:do{if((c[F+4>>2]&-8|0)!=(D|0)){d=D<<H;e=F;while(1){I=e+(d>>>31<<2)+16|0;j=c[I>>2]|0;if((j|0)==0){break}if((c[j+4>>2]&-8|0)==(D|0)){J=j;break b}else{d=d<<1;e=j}}if(I>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[I>>2]=p;c[p+24>>2]=e;c[p+12>>2]=p;c[p+8>>2]=p;break a}}else{J=F}}while(0);F=J+8|0;d=c[F>>2]|0;j=c[6016>>2]|0;if(J>>>0<j>>>0){pb()}if(d>>>0<j>>>0){pb()}else{c[d+12>>2]=p;c[F>>2]=p;c[p+8>>2]=d;c[p+12>>2]=J;c[p+24>>2]=0;break}}else{c[6004>>2]=E|w;c[C>>2]=p;c[p+24>>2]=C;c[p+12>>2]=p;c[p+8>>2]=p}}while(0);p=(c[6032>>2]|0)+ -1|0;c[6032>>2]=p;if((p|0)==0){K=6456|0}else{i=b;return}while(1){p=c[K>>2]|0;if((p|0)==0){break}else{K=p+8|0}}c[6032>>2]=-1;i=b;return}function Hh(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0;d=i;do{if((a|0)!=0){if(b>>>0>4294967231){c[(Pa()|0)>>2]=12;e=0;break}if(b>>>0<11){f=16}else{f=b+11&-8}g=Ih(a+ -8|0,f)|0;if((g|0)!=0){e=g+8|0;break}g=Fh(b)|0;if((g|0)==0){e=0}else{h=c[a+ -4>>2]|0;j=(h&-8)-((h&3|0)==0?8:4)|0;Qh(g|0,a|0,(j>>>0<b>>>0?j:b)|0)|0;Gh(a);e=g}}else{e=Fh(b)|0}}while(0);i=d;return e|0}function Ih(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0;d=i;e=a+4|0;f=c[e>>2]|0;g=f&-8;h=a+g|0;j=c[6016>>2]|0;if(a>>>0<j>>>0){pb()}k=f&3;if(!((k|0)!=1&a>>>0<h>>>0)){pb()}l=a+(g|4)|0;m=c[l>>2]|0;if((m&1|0)==0){pb()}if((k|0)==0){if(b>>>0<256){n=0;i=d;return n|0}if(!(g>>>0<(b+4|0)>>>0)?!((g-b|0)>>>0>c[6480>>2]<<1>>>0):0){n=a;i=d;return n|0}n=0;i=d;return n|0}if(!(g>>>0<b>>>0)){k=g-b|0;if(!(k>>>0>15)){n=a;i=d;return n|0}c[e>>2]=f&1|b|2;c[a+(b+4)>>2]=k|3;c[l>>2]=c[l>>2]|1;Jh(a+b|0,k);n=a;i=d;return n|0}if((h|0)==(c[6024>>2]|0)){k=(c[6012>>2]|0)+g|0;if(!(k>>>0>b>>>0)){n=0;i=d;return n|0}l=k-b|0;c[e>>2]=f&1|b|2;c[a+(b+4)>>2]=l|1;c[6024>>2]=a+b;c[6012>>2]=l;n=a;i=d;return n|0}if((h|0)==(c[6020>>2]|0)){l=(c[6008>>2]|0)+g|0;if(l>>>0<b>>>0){n=0;i=d;return n|0}k=l-b|0;if(k>>>0>15){c[e>>2]=f&1|b|2;c[a+(b+4)>>2]=k|1;c[a+l>>2]=k;o=a+(l+4)|0;c[o>>2]=c[o>>2]&-2;p=a+b|0;q=k}else{c[e>>2]=f&1|l|2;f=a+(l+4)|0;c[f>>2]=c[f>>2]|1;p=0;q=0}c[6008>>2]=q;c[6020>>2]=p;n=a;i=d;return n|0}if((m&2|0)!=0){n=0;i=d;return n|0}p=(m&-8)+g|0;if(p>>>0<b>>>0){n=0;i=d;return n|0}q=p-b|0;f=m>>>3;do{if(!(m>>>0<256)){l=c[a+(g+24)>>2]|0;k=c[a+(g+12)>>2]|0;do{if((k|0)==(h|0)){o=a+(g+20)|0;r=c[o>>2]|0;if((r|0)==0){s=a+(g+16)|0;t=c[s>>2]|0;if((t|0)==0){u=0;break}else{v=t;w=s}}else{v=r;w=o}while(1){o=v+20|0;r=c[o>>2]|0;if((r|0)!=0){v=r;w=o;continue}o=v+16|0;r=c[o>>2]|0;if((r|0)==0){break}else{v=r;w=o}}if(w>>>0<j>>>0){pb()}else{c[w>>2]=0;u=v;break}}else{o=c[a+(g+8)>>2]|0;if(o>>>0<j>>>0){pb()}r=o+12|0;if((c[r>>2]|0)!=(h|0)){pb()}s=k+8|0;if((c[s>>2]|0)==(h|0)){c[r>>2]=k;c[s>>2]=o;u=k;break}else{pb()}}}while(0);if((l|0)!=0){k=c[a+(g+28)>>2]|0;o=6304+(k<<2)|0;if((h|0)==(c[o>>2]|0)){c[o>>2]=u;if((u|0)==0){c[6004>>2]=c[6004>>2]&~(1<<k);break}}else{if(l>>>0<(c[6016>>2]|0)>>>0){pb()}k=l+16|0;if((c[k>>2]|0)==(h|0)){c[k>>2]=u}else{c[l+20>>2]=u}if((u|0)==0){break}}if(u>>>0<(c[6016>>2]|0)>>>0){pb()}c[u+24>>2]=l;k=c[a+(g+16)>>2]|0;do{if((k|0)!=0){if(k>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[u+16>>2]=k;c[k+24>>2]=u;break}}}while(0);k=c[a+(g+20)>>2]|0;if((k|0)!=0){if(k>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[u+20>>2]=k;c[k+24>>2]=u;break}}}}else{k=c[a+(g+8)>>2]|0;l=c[a+(g+12)>>2]|0;o=6040+(f<<1<<2)|0;if((k|0)!=(o|0)){if(k>>>0<j>>>0){pb()}if((c[k+12>>2]|0)!=(h|0)){pb()}}if((l|0)==(k|0)){c[1500]=c[1500]&~(1<<f);break}if((l|0)!=(o|0)){if(l>>>0<j>>>0){pb()}o=l+8|0;if((c[o>>2]|0)==(h|0)){x=o}else{pb()}}else{x=l+8|0}c[k+12>>2]=l;c[x>>2]=k}}while(0);if(q>>>0<16){c[e>>2]=p|c[e>>2]&1|2;x=a+(p|4)|0;c[x>>2]=c[x>>2]|1;n=a;i=d;return n|0}else{c[e>>2]=c[e>>2]&1|b|2;c[a+(b+4)>>2]=q|3;e=a+(p|4)|0;c[e>>2]=c[e>>2]|1;Jh(a+b|0,q);n=a;i=d;return n|0}return 0}function Jh(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0;d=i;e=a+b|0;f=c[a+4>>2]|0;do{if((f&1|0)==0){g=c[a>>2]|0;if((f&3|0)==0){i=d;return}h=a+(0-g)|0;j=g+b|0;k=c[6016>>2]|0;if(h>>>0<k>>>0){pb()}if((h|0)==(c[6020>>2]|0)){l=a+(b+4)|0;if((c[l>>2]&3|0)!=3){m=h;n=j;break}c[6008>>2]=j;c[l>>2]=c[l>>2]&-2;c[a+(4-g)>>2]=j|1;c[e>>2]=j;i=d;return}l=g>>>3;if(g>>>0<256){o=c[a+(8-g)>>2]|0;p=c[a+(12-g)>>2]|0;q=6040+(l<<1<<2)|0;if((o|0)!=(q|0)){if(o>>>0<k>>>0){pb()}if((c[o+12>>2]|0)!=(h|0)){pb()}}if((p|0)==(o|0)){c[1500]=c[1500]&~(1<<l);m=h;n=j;break}if((p|0)!=(q|0)){if(p>>>0<k>>>0){pb()}q=p+8|0;if((c[q>>2]|0)==(h|0)){r=q}else{pb()}}else{r=p+8|0}c[o+12>>2]=p;c[r>>2]=o;m=h;n=j;break}o=c[a+(24-g)>>2]|0;p=c[a+(12-g)>>2]|0;do{if((p|0)==(h|0)){q=16-g|0;l=a+(q+4)|0;s=c[l>>2]|0;if((s|0)==0){t=a+q|0;q=c[t>>2]|0;if((q|0)==0){u=0;break}else{v=q;w=t}}else{v=s;w=l}while(1){l=v+20|0;s=c[l>>2]|0;if((s|0)!=0){v=s;w=l;continue}l=v+16|0;s=c[l>>2]|0;if((s|0)==0){break}else{v=s;w=l}}if(w>>>0<k>>>0){pb()}else{c[w>>2]=0;u=v;break}}else{l=c[a+(8-g)>>2]|0;if(l>>>0<k>>>0){pb()}s=l+12|0;if((c[s>>2]|0)!=(h|0)){pb()}t=p+8|0;if((c[t>>2]|0)==(h|0)){c[s>>2]=p;c[t>>2]=l;u=p;break}else{pb()}}}while(0);if((o|0)!=0){p=c[a+(28-g)>>2]|0;k=6304+(p<<2)|0;if((h|0)==(c[k>>2]|0)){c[k>>2]=u;if((u|0)==0){c[6004>>2]=c[6004>>2]&~(1<<p);m=h;n=j;break}}else{if(o>>>0<(c[6016>>2]|0)>>>0){pb()}p=o+16|0;if((c[p>>2]|0)==(h|0)){c[p>>2]=u}else{c[o+20>>2]=u}if((u|0)==0){m=h;n=j;break}}if(u>>>0<(c[6016>>2]|0)>>>0){pb()}c[u+24>>2]=o;p=16-g|0;k=c[a+p>>2]|0;do{if((k|0)!=0){if(k>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[u+16>>2]=k;c[k+24>>2]=u;break}}}while(0);k=c[a+(p+4)>>2]|0;if((k|0)!=0){if(k>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[u+20>>2]=k;c[k+24>>2]=u;m=h;n=j;break}}else{m=h;n=j}}else{m=h;n=j}}else{m=a;n=b}}while(0);u=c[6016>>2]|0;if(e>>>0<u>>>0){pb()}v=a+(b+4)|0;w=c[v>>2]|0;if((w&2|0)==0){if((e|0)==(c[6024>>2]|0)){r=(c[6012>>2]|0)+n|0;c[6012>>2]=r;c[6024>>2]=m;c[m+4>>2]=r|1;if((m|0)!=(c[6020>>2]|0)){i=d;return}c[6020>>2]=0;c[6008>>2]=0;i=d;return}if((e|0)==(c[6020>>2]|0)){r=(c[6008>>2]|0)+n|0;c[6008>>2]=r;c[6020>>2]=m;c[m+4>>2]=r|1;c[m+r>>2]=r;i=d;return}r=(w&-8)+n|0;f=w>>>3;do{if(!(w>>>0<256)){k=c[a+(b+24)>>2]|0;g=c[a+(b+12)>>2]|0;do{if((g|0)==(e|0)){o=a+(b+20)|0;l=c[o>>2]|0;if((l|0)==0){t=a+(b+16)|0;s=c[t>>2]|0;if((s|0)==0){x=0;break}else{y=s;z=t}}else{y=l;z=o}while(1){o=y+20|0;l=c[o>>2]|0;if((l|0)!=0){y=l;z=o;continue}o=y+16|0;l=c[o>>2]|0;if((l|0)==0){break}else{y=l;z=o}}if(z>>>0<u>>>0){pb()}else{c[z>>2]=0;x=y;break}}else{o=c[a+(b+8)>>2]|0;if(o>>>0<u>>>0){pb()}l=o+12|0;if((c[l>>2]|0)!=(e|0)){pb()}t=g+8|0;if((c[t>>2]|0)==(e|0)){c[l>>2]=g;c[t>>2]=o;x=g;break}else{pb()}}}while(0);if((k|0)!=0){g=c[a+(b+28)>>2]|0;j=6304+(g<<2)|0;if((e|0)==(c[j>>2]|0)){c[j>>2]=x;if((x|0)==0){c[6004>>2]=c[6004>>2]&~(1<<g);break}}else{if(k>>>0<(c[6016>>2]|0)>>>0){pb()}g=k+16|0;if((c[g>>2]|0)==(e|0)){c[g>>2]=x}else{c[k+20>>2]=x}if((x|0)==0){break}}if(x>>>0<(c[6016>>2]|0)>>>0){pb()}c[x+24>>2]=k;g=c[a+(b+16)>>2]|0;do{if((g|0)!=0){if(g>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[x+16>>2]=g;c[g+24>>2]=x;break}}}while(0);g=c[a+(b+20)>>2]|0;if((g|0)!=0){if(g>>>0<(c[6016>>2]|0)>>>0){pb()}else{c[x+20>>2]=g;c[g+24>>2]=x;break}}}}else{g=c[a+(b+8)>>2]|0;k=c[a+(b+12)>>2]|0;j=6040+(f<<1<<2)|0;if((g|0)!=(j|0)){if(g>>>0<u>>>0){pb()}if((c[g+12>>2]|0)!=(e|0)){pb()}}if((k|0)==(g|0)){c[1500]=c[1500]&~(1<<f);break}if((k|0)!=(j|0)){if(k>>>0<u>>>0){pb()}j=k+8|0;if((c[j>>2]|0)==(e|0)){A=j}else{pb()}}else{A=k+8|0}c[g+12>>2]=k;c[A>>2]=g}}while(0);c[m+4>>2]=r|1;c[m+r>>2]=r;if((m|0)==(c[6020>>2]|0)){c[6008>>2]=r;i=d;return}else{B=r}}else{c[v>>2]=w&-2;c[m+4>>2]=n|1;c[m+n>>2]=n;B=n}n=B>>>3;if(B>>>0<256){w=n<<1;v=6040+(w<<2)|0;r=c[1500]|0;A=1<<n;if((r&A|0)!=0){n=6040+(w+2<<2)|0;e=c[n>>2]|0;if(e>>>0<(c[6016>>2]|0)>>>0){pb()}else{C=n;D=e}}else{c[1500]=r|A;C=6040+(w+2<<2)|0;D=v}c[C>>2]=m;c[D+12>>2]=m;c[m+8>>2]=D;c[m+12>>2]=v;i=d;return}v=B>>>8;if((v|0)!=0){if(B>>>0>16777215){E=31}else{D=(v+1048320|0)>>>16&8;C=v<<D;v=(C+520192|0)>>>16&4;w=C<<v;C=(w+245760|0)>>>16&2;A=14-(v|D|C)+(w<<C>>>15)|0;E=B>>>(A+7|0)&1|A<<1}}else{E=0}A=6304+(E<<2)|0;c[m+28>>2]=E;c[m+20>>2]=0;c[m+16>>2]=0;C=c[6004>>2]|0;w=1<<E;if((C&w|0)==0){c[6004>>2]=C|w;c[A>>2]=m;c[m+24>>2]=A;c[m+12>>2]=m;c[m+8>>2]=m;i=d;return}w=c[A>>2]|0;if((E|0)==31){F=0}else{F=25-(E>>>1)|0}a:do{if((c[w+4>>2]&-8|0)==(B|0)){G=w}else{E=B<<F;A=w;while(1){H=A+(E>>>31<<2)+16|0;C=c[H>>2]|0;if((C|0)==0){break}if((c[C+4>>2]&-8|0)==(B|0)){G=C;break a}else{E=E<<1;A=C}}if(H>>>0<(c[6016>>2]|0)>>>0){pb()}c[H>>2]=m;c[m+24>>2]=A;c[m+12>>2]=m;c[m+8>>2]=m;i=d;return}}while(0);H=G+8|0;B=c[H>>2]|0;w=c[6016>>2]|0;if(G>>>0<w>>>0){pb()}if(B>>>0<w>>>0){pb()}c[B+12>>2]=m;c[H>>2]=m;c[m+8>>2]=B;c[m+12>>2]=G;c[m+24>>2]=0;i=d;return}function Kh(b){b=b|0;var c=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;c=i;d=b;while(1){e=d+1|0;if(($a(a[d]|0)|0)==0){break}else{d=e}}b=a[d]|0;f=b<<24>>24;if((f|0)==45){g=1;h=5}else if((f|0)==43){g=0;h=5}else{j=d;k=b;l=0}if((h|0)==5){j=e;k=a[e]|0;l=g}if((tb(k<<24>>24|0)|0)==0){m=0;n=(l|0)!=0;o=0-m|0;p=n?m:o;i=c;return p|0}else{q=j;r=0}while(1){j=q+1|0;k=(r*10|0)+48-(a[q]|0)|0;if((tb(a[j]|0)|0)==0){m=k;break}else{q=j;r=k}}n=(l|0)!=0;o=0-m|0;p=n?m:o;i=c;return p|0}function Lh(b,c){b=b|0;c=c|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;d=i;e=a[b]|0;f=a[c]|0;if(e<<24>>24!=f<<24>>24|e<<24>>24==0|f<<24>>24==0){g=e;h=f;j=g&255;k=h&255;l=j-k|0;i=d;return l|0}else{m=b;n=c}while(1){c=m+1|0;b=n+1|0;f=a[c]|0;e=a[b]|0;if(f<<24>>24!=e<<24>>24|f<<24>>24==0|e<<24>>24==0){g=f;h=e;break}else{m=c;n=b}}j=g&255;k=h&255;l=j-k|0;i=d;return l|0}function Mh(){}function Nh(b){b=b|0;var c=0;c=b;while(a[c]|0){c=c+1|0}return c-b|0}function Oh(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,i=0;f=b+e|0;if((e|0)>=20){d=d&255;g=b&3;h=d|d<<8|d<<16|d<<24;i=f&~3;if(g){g=b+4-g|0;while((b|0)<(g|0)){a[b]=d;b=b+1|0}}while((b|0)<(i|0)){c[b>>2]=h;b=b+4|0}}while((b|0)<(f|0)){a[b]=d;b=b+1|0}return b-e|0}function Ph(b,c){b=b|0;c=c|0;var d=0,e=0;d=b+(Nh(b)|0)|0;do{a[d+e|0]=a[c+e|0];e=e+1|0}while(a[c+(e-1)|0]|0);return b|0}function Qh(b,d,e){b=b|0;d=d|0;e=e|0;var f=0;if((e|0)>=4096)return Qa(b|0,d|0,e|0)|0;f=b|0;if((b&3)==(d&3)){while(b&3){if((e|0)==0)return f|0;a[b]=a[d]|0;b=b+1|0;d=d+1|0;e=e-1|0}while((e|0)>=4){c[b>>2]=c[d>>2];b=b+4|0;d=d+4|0;e=e-4|0}}while((e|0)>0){a[b]=a[d]|0;b=b+1|0;d=d+1|0;e=e-1|0}return f|0}function Rh(b,c){b=b|0;c=c|0;var d=0;do{a[b+d|0]=a[c+d|0];d=d+1|0}while(a[c+(d-1)|0]|0);return b|0}function Sh(a,b,c,d,e){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;return Db[a&3](b|0,c|0,d|0,e|0)|0}function Th(a,b,c,d,e,f){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;Eb[a&31](b|0,c|0,d|0,e|0,f|0)}function Uh(a){a=a|0;return Fb[a&1]()|0}function Vh(a,b){a=a|0;b=b|0;Gb[a&7](b|0)}function Wh(a,b,c){a=a|0;b=b|0;c=c|0;Hb[a&7](b|0,c|0)}function Xh(a,b,c,d,e,f,g){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;g=g|0;return Ib[a&1](b|0,c|0,d|0,e|0,f|0,g|0)|0}function Yh(a,b,c,d,e,f,g,h){a=a|0;b=b|0;c=+c;d=+d;e=+e;f=+f;g=+g;h=h|0;Jb[a&1](b|0,+c,+d,+e,+f,+g,h|0)}function Zh(a,b,c,d,e,f,g,h,i){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;g=g|0;h=+h;i=+i;Kb[a&1](b|0,c|0,d|0,e|0,f|0,g|0,+h,+i)}function _h(a,b){a=a|0;b=b|0;return Lb[a&15](b|0)|0}function $h(a,b,c,d){a=a|0;b=b|0;c=c|0;d=d|0;return Mb[a&31](b|0,c|0,d|0)|0}function ai(a,b,c,d){a=a|0;b=b|0;c=c|0;d=d|0;Nb[a&3](b|0,c|0,d|0)}function bi(a,b,c,d,e,f,g,h,i){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;i=i|0;Ob[a&1](b|0,c|0,d|0,e|0,f|0,g|0,h|0,i|0)}function ci(a,b,c,d,e,f,g){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;g=g|0;Pb[a&3](b|0,c|0,d|0,e|0,f|0,g|0)}function di(a,b,c){a=a|0;b=b|0;c=c|0;return Qb[a&15](b|0,c|0)|0}function ei(a,b,c,d,e){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;return+Rb[a&3](b|0,c|0,d|0,e|0)}function fi(a,b,c,d,e){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;Sb[a&7](b|0,c|0,d|0,e|0)}function gi(a,b,c,d){a=a|0;b=b|0;c=c|0;d=d|0;_(0);return 0}function hi(a,b,c,d,e){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;_(1)}function ii(){_(2);return 0}function ji(a){a=a|0;_(3)}function ki(a,b){a=a|0;b=b|0;_(4)}function li(a,b,c,d,e,f){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;_(5);return 0}function mi(a,b,c,d,e,f,g){a=a|0;b=+b;c=+c;d=+d;e=+e;f=+f;g=g|0;_(6)}function ni(a,b,c,d,e,f,g,h){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;g=+g;h=+h;_(7)}function oi(a){a=a|0;_(8);return 0}function pi(a,b,c){a=a|0;b=b|0;c=c|0;_(9);return 0}function qi(a,b,c){a=a|0;b=b|0;c=c|0;_(10)}function ri(a,b,c,d,e,f,g,h){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;_(11)}function si(a,b,c,d,e,f){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;_(12)}function ti(a,b){a=a|0;b=b|0;_(13);return 0}function ui(a,b,c,d){a=a|0;b=b|0;c=c|0;d=d|0;_(14);return 0.0}function vi(a,b,c,d){a=a|0;b=b|0;c=c|0;d=d|0;_(15)}




// EMSCRIPTEN_END_FUNCS
var Db=[gi,He,Me,qd];var Eb=[hi,Qc,Rc,Sc,Tc,Uc,Vc,Wc,Xc,Yc,Zc,_c,$c,ad,Vd,Xd,Yd,hi,hi,hi,hi,hi,hi,hi,hi,hi,hi,hi,hi,hi,hi,hi];var Fb=[ii,ye];var Gb=[ji,Zd,_d,$d,Ce,Le,Qe,oe];var Hb=[ki,ae,ce,Ae,Se,_e,ki,ki];var Ib=[li,Ue];var Jb=[mi,ge];var Kb=[ni,$e];var Lb=[oi,De,Ee,Fe,Ke,Ne,Oe,Pe,Re,cf,Bf,Cf,Df,Ef,oi,oi];var Mb=[pi,cd,dd,ed,fd,gd,hd,id,jd,kd,ld,md,nd,od,be,fe,ze,Je,pi,pi,pi,pi,pi,pi,pi,pi,pi,pi,pi,pi,pi,pi];var Nb=[qi,Te,df,ef];var Ob=[ri,Sd];var Pb=[si,Td,Ud,Wd];var Qb=[ti,Be,Ge,Ie,Ve,Ye,Ze,ff,sd,wd,se,te,ti,ti,ti,ti];var Rb=[ui,af,bf,ui];var Sb=[vi,de,ee,We,Xe,vi,vi,vi];return{_malloc:Fh,_restore_puzzle_size:Kd,_strcat:Ph,_resize_puzzle:Jd,_command:ke,_timer_callback:Id,_key:Rd,_realloc:Hh,_strlen:Nh,_memset:Oh,_dlg_return_ival:je,_free:Gh,_mousedown:Nd,_mouseup:Pd,_dlg_return_sval:ie,_mousemove:Qd,_memcpy:Qh,_strcpy:Rh,_main:ne,runPostSets:Mh,stackAlloc:Tb,stackSave:Ub,stackRestore:Vb,setThrew:Wb,setTempRet0:Zb,setTempRet1:_b,setTempRet2:$b,setTempRet3:ac,setTempRet4:bc,setTempRet5:cc,setTempRet6:dc,setTempRet7:ec,setTempRet8:fc,setTempRet9:gc,dynCall_iiiii:Sh,dynCall_viiiii:Th,dynCall_i:Uh,dynCall_vi:Vh,dynCall_vii:Wh,dynCall_iiiiiii:Xh,dynCall_vidddddi:Yh,dynCall_viiiiiidd:Zh,dynCall_ii:_h,dynCall_iiii:$h,dynCall_viii:ai,dynCall_viiiiiiii:bi,dynCall_viiiiii:ci,dynCall_iii:di,dynCall_diiii:ei,dynCall_viiii:fi}})


// EMSCRIPTEN_END_ASM
({ "Math": Math, "Int8Array": Int8Array, "Int16Array": Int16Array, "Int32Array": Int32Array, "Uint8Array": Uint8Array, "Uint16Array": Uint16Array, "Uint32Array": Uint32Array, "Float32Array": Float32Array, "Float64Array": Float64Array }, { "abort": abort, "assert": assert, "asmPrintInt": asmPrintInt, "asmPrintFloat": asmPrintFloat, "min": Math_min, "invoke_iiiii": invoke_iiiii, "invoke_viiiii": invoke_viiiii, "invoke_i": invoke_i, "invoke_vi": invoke_vi, "invoke_vii": invoke_vii, "invoke_iiiiiii": invoke_iiiiiii, "invoke_vidddddi": invoke_vidddddi, "invoke_viiiiiidd": invoke_viiiiiidd, "invoke_ii": invoke_ii, "invoke_iiii": invoke_iiii, "invoke_viii": invoke_viii, "invoke_viiiiiiii": invoke_viiiiiiii, "invoke_viiiiii": invoke_viiiiii, "invoke_iii": invoke_iii, "invoke_diiii": invoke_diiii, "invoke_viiii": invoke_viiii, "_fabs": _fabs, "_js_error_box": _js_error_box, "_js_dialog_cleanup": _js_dialog_cleanup, "_js_select_preset": _js_select_preset, "_js_dialog_init": _js_dialog_init, "_js_canvas_draw_line": _js_canvas_draw_line, "__reallyNegative": __reallyNegative, "_ceil": _ceil, "_js_canvas_find_font_midpoint": _js_canvas_find_font_midpoint, "___assert_fail": ___assert_fail, "___buildEnvironment": ___buildEnvironment, "_js_focus_canvas": _js_focus_canvas, "_js_canvas_set_size": _js_canvas_set_size, "_js_dialog_launch": _js_dialog_launch, "_js_get_selected_preset": _js_get_selected_preset, "_js_canvas_draw_circle": _js_canvas_draw_circle, "_js_canvas_draw_rect": _js_canvas_draw_rect, "_sscanf": _sscanf, "_sbrk": _sbrk, "_js_dialog_boolean": _js_dialog_boolean, "_js_canvas_new_blitter": _js_canvas_new_blitter, "_snprintf": _snprintf, "___errno_location": ___errno_location, "_emscripten_memcpy_big": _emscripten_memcpy_big, "_js_canvas_make_statusbar": _js_canvas_make_statusbar, "_js_remove_type_dropdown": _js_remove_type_dropdown, "_sysconf": _sysconf, "_js_canvas_unclip": _js_canvas_unclip, "___setErrNo": ___setErrNo, "_js_canvas_draw_text": _js_canvas_draw_text, "_js_dialog_string": _js_dialog_string, "_floor": _floor, "_js_canvas_draw_update": _js_canvas_draw_update, "_js_update_permalinks": _js_update_permalinks, "_isspace": _isspace, "_js_remove_solve_button": _js_remove_solve_button, "_getenv": _getenv, "_sprintf": _sprintf, "_js_canvas_start_draw": _js_canvas_start_draw, "_js_enable_undo_redo": _js_enable_undo_redo, "_toupper": _toupper, "_js_get_date_64": _js_get_date_64, "_fflush": _fflush, "__scanString": __scanString, "_js_deactivate_timer": _js_deactivate_timer, "_vsnprintf": _vsnprintf, "_js_canvas_copy_from_blitter": _js_canvas_copy_from_blitter, "_js_activate_timer": _js_activate_timer, "_js_canvas_end_draw": _js_canvas_end_draw, "__getFloat": __getFloat, "_abort": _abort, "_js_dialog_choices": _js_dialog_choices, "_js_canvas_copy_to_blitter": _js_canvas_copy_to_blitter, "_time": _time, "_isdigit": _isdigit, "_js_canvas_set_statusbar": _js_canvas_set_statusbar, "_abs": _abs, "__formatString": __formatString, "_js_canvas_clip_rect": _js_canvas_clip_rect, "_sqrt": _sqrt, "_js_canvas_draw_poly": _js_canvas_draw_poly, "_js_canvas_free_blitter": _js_canvas_free_blitter, "_js_add_preset": _js_add_preset, "STACKTOP": STACKTOP, "STACK_MAX": STACK_MAX, "tempDoublePtr": tempDoublePtr, "ABORT": ABORT, "NaN": NaN, "Infinity": Infinity }, buffer);
var _malloc = Module["_malloc"] = asm["_malloc"];
var _restore_puzzle_size = Module["_restore_puzzle_size"] = asm["_restore_puzzle_size"];
var _strcat = Module["_strcat"] = asm["_strcat"];
var _resize_puzzle = Module["_resize_puzzle"] = asm["_resize_puzzle"];
var _command = Module["_command"] = asm["_command"];
var _timer_callback = Module["_timer_callback"] = asm["_timer_callback"];
var _key = Module["_key"] = asm["_key"];
var _realloc = Module["_realloc"] = asm["_realloc"];
var _strlen = Module["_strlen"] = asm["_strlen"];
var _memset = Module["_memset"] = asm["_memset"];
var _dlg_return_ival = Module["_dlg_return_ival"] = asm["_dlg_return_ival"];
var _free = Module["_free"] = asm["_free"];
var _mousedown = Module["_mousedown"] = asm["_mousedown"];
var _mouseup = Module["_mouseup"] = asm["_mouseup"];
var _dlg_return_sval = Module["_dlg_return_sval"] = asm["_dlg_return_sval"];
var _mousemove = Module["_mousemove"] = asm["_mousemove"];
var _memcpy = Module["_memcpy"] = asm["_memcpy"];
var _strcpy = Module["_strcpy"] = asm["_strcpy"];
var _main = Module["_main"] = asm["_main"];
var runPostSets = Module["runPostSets"] = asm["runPostSets"];
var dynCall_iiiii = Module["dynCall_iiiii"] = asm["dynCall_iiiii"];
var dynCall_viiiii = Module["dynCall_viiiii"] = asm["dynCall_viiiii"];
var dynCall_i = Module["dynCall_i"] = asm["dynCall_i"];
var dynCall_vi = Module["dynCall_vi"] = asm["dynCall_vi"];
var dynCall_vii = Module["dynCall_vii"] = asm["dynCall_vii"];
var dynCall_iiiiiii = Module["dynCall_iiiiiii"] = asm["dynCall_iiiiiii"];
var dynCall_vidddddi = Module["dynCall_vidddddi"] = asm["dynCall_vidddddi"];
var dynCall_viiiiiidd = Module["dynCall_viiiiiidd"] = asm["dynCall_viiiiiidd"];
var dynCall_ii = Module["dynCall_ii"] = asm["dynCall_ii"];
var dynCall_iiii = Module["dynCall_iiii"] = asm["dynCall_iiii"];
var dynCall_viii = Module["dynCall_viii"] = asm["dynCall_viii"];
var dynCall_viiiiiiii = Module["dynCall_viiiiiiii"] = asm["dynCall_viiiiiiii"];
var dynCall_viiiiii = Module["dynCall_viiiiii"] = asm["dynCall_viiiiii"];
var dynCall_iii = Module["dynCall_iii"] = asm["dynCall_iii"];
var dynCall_diiii = Module["dynCall_diiii"] = asm["dynCall_diiii"];
var dynCall_viiii = Module["dynCall_viiii"] = asm["dynCall_viiii"];

Runtime.stackAlloc = function(size) { return asm['stackAlloc'](size) };
Runtime.stackSave = function() { return asm['stackSave']() };
Runtime.stackRestore = function(top) { asm['stackRestore'](top) };


// Warning: printing of i64 values may be slightly rounded! No deep i64 math used, so precise i64 code not included
var i64Math = null;

// === Auto-generated postamble setup entry stuff ===

if (memoryInitializer) {
  if (ENVIRONMENT_IS_NODE || ENVIRONMENT_IS_SHELL) {
    var data = Module['readBinary'](memoryInitializer);
    HEAPU8.set(data, STATIC_BASE);
  } else {
    addRunDependency('memory initializer');
    Browser.asyncLoad(memoryInitializer, function(data) {
      HEAPU8.set(data, STATIC_BASE);
      removeRunDependency('memory initializer');
    }, function(data) {
      throw 'could not load memory initializer ' + memoryInitializer;
    });
  }
}

function ExitStatus(status) {
  this.name = "ExitStatus";
  this.message = "Program terminated with exit(" + status + ")";
  this.status = status;
};
ExitStatus.prototype = new Error();
ExitStatus.prototype.constructor = ExitStatus;

var initialStackTop;
var preloadStartTime = null;
var calledMain = false;

dependenciesFulfilled = function runCaller() {
  // If run has never been called, and we should call run (INVOKE_RUN is true, and Module.noInitialRun is not false)
  if (!Module['calledRun'] && shouldRunNow) run();
  if (!Module['calledRun']) dependenciesFulfilled = runCaller; // try this again later, after new deps are fulfilled
}

Module['callMain'] = Module.callMain = function callMain(args) {
  assert(runDependencies == 0, 'cannot call main when async dependencies remain! (listen on __ATMAIN__)');
  assert(__ATPRERUN__.length == 0, 'cannot call main when preRun functions remain to be called');

  args = args || [];

  ensureInitRuntime();

  var argc = args.length+1;
  function pad() {
    for (var i = 0; i < 4-1; i++) {
      argv.push(0);
    }
  }
  var argv = [allocate(intArrayFromString("/bin/this.program"), 'i8', ALLOC_NORMAL) ];
  pad();
  for (var i = 0; i < argc-1; i = i + 1) {
    argv.push(allocate(intArrayFromString(args[i]), 'i8', ALLOC_NORMAL));
    pad();
  }
  argv.push(0);
  argv = allocate(argv, 'i32', ALLOC_NORMAL);

  initialStackTop = STACKTOP;

  try {

    var ret = Module['_main'](argc, argv, 0);


    // if we're not running an evented main loop, it's time to exit
    if (!Module['noExitRuntime']) {
      exit(ret);
    }
  }
  catch(e) {
    if (e instanceof ExitStatus) {
      // exit() throws this once it's done to make sure execution
      // has been stopped completely
      return;
    } else if (e == 'SimulateInfiniteLoop') {
      // running an evented main loop, don't immediately exit
      Module['noExitRuntime'] = true;
      return;
    } else {
      if (e && typeof e === 'object' && e.stack) Module.printErr('exception thrown: ' + [e, e.stack]);
      throw e;
    }
  } finally {
    calledMain = true;
  }
}




function run(args) {
  args = args || Module['arguments'];

  if (preloadStartTime === null) preloadStartTime = Date.now();

  if (runDependencies > 0) {
    Module.printErr('run() called, but dependencies remain, so not running');
    return;
  }

  preRun();

  if (runDependencies > 0) return; // a preRun added a dependency, run will be called later
  if (Module['calledRun']) return; // run may have just been called through dependencies being fulfilled just in this very frame

  function doRun() {
    if (Module['calledRun']) return; // run may have just been called while the async setStatus time below was happening
    Module['calledRun'] = true;

    ensureInitRuntime();

    preMain();

    if (ENVIRONMENT_IS_WEB && preloadStartTime !== null) {
      Module.printErr('pre-main prep time: ' + (Date.now() - preloadStartTime) + ' ms');
    }

    if (Module['_main'] && shouldRunNow) {
      Module['callMain'](args);
    }

    postRun();
  }

  if (Module['setStatus']) {
    Module['setStatus']('Running...');
    setTimeout(function() {
      setTimeout(function() {
        Module['setStatus']('');
      }, 1);
      if (!ABORT) doRun();
    }, 1);
  } else {
    doRun();
  }
}
Module['run'] = Module.run = run;

function exit(status) {
  ABORT = true;
  EXITSTATUS = status;
  STACKTOP = initialStackTop;

  // exit the runtime
  exitRuntime();

  // TODO We should handle this differently based on environment.
  // In the browser, the best we can do is throw an exception
  // to halt execution, but in node we could process.exit and
  // I'd imagine SM shell would have something equivalent.
  // This would let us set a proper exit status (which
  // would be great for checking test exit statuses).
  // https://github.com/kripken/emscripten/issues/1371

  // throw an exception to halt the current execution
  throw new ExitStatus(status);
}
Module['exit'] = Module.exit = exit;

function abort(text) {
  if (text) {
    Module.print(text);
    Module.printErr(text);
  }

  ABORT = true;
  EXITSTATUS = 1;

  var extra = '\nIf this abort() is unexpected, build with -s ASSERTIONS=1 which can give more information.';

  throw 'abort() at ' + stackTrace() + extra;
}
Module['abort'] = Module.abort = abort;

// {{PRE_RUN_ADDITIONS}}

if (Module['preInit']) {
  if (typeof Module['preInit'] == 'function') Module['preInit'] = [Module['preInit']];
  while (Module['preInit'].length > 0) {
    Module['preInit'].pop()();
  }
}

// shouldRunNow refers to calling main(), not run().
var shouldRunNow = true;
if (Module['noInitialRun']) {
  shouldRunNow = false;
}


run();

// {{POST_RUN_ADDITIONS}}






// {{MODULE_ADDITIONS}}

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

    // Stop right-clicks on the puzzle from popping up a context menu.
    // We need those right-clicks!
    onscreen_canvas.oncontextmenu = function(event) { return false; }

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
    resizable_div.appendChild(resize_handle);
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

STATICTOP = STATIC_BASE + Runtime.alignMemory(8947);
/* global initializers */ __ATINIT__.push();


/* memory initializer */ allocate([119,104,32,61,61,32,107,42,110,0,0,0,0,0,0,0,100,105,118,118,121,46,99,0,100,105,118,118,121,95,105,110,116,101,114,110,97,108,0,0,119,104,32,62,61,32,50,42,110,0,0,0,0,0,0,0,111,119,110,91,116,109,112,115,113,93,32,61,61,32,106,0,113,116,97,105,108,32,60,32,110,0,0,0,0,0,0,0,111,119,110,91,105,93,32,62,61,32,48,32,38,38,32,111,119,110,91,105,93,32,60,32,110,0,0,0,0,0,0,0,100,115,102,95,99,97,110,111,110,105,102,121,40,116,109,112,44,32,106,41,32,61,61,32,100,115,102,95,99,97,110,111,110,105,102,121,40,116,109,112,44,32,105,41,0,0,0,0,100,114,97,119,105,110,103,46,99,0,0,0,0,0,0,0,100,114,45,62,109,101,0,0,115,116,97,116,117,115,95,98,97,114,0,0,0,0,0,0,105,110,100,101,120,32,62,61,32,48,0,0,0,0,0,0,100,115,102,46,99,0,0,0,101,100,115,102,95,99,97,110,111,110,105,102,121,0,0,0,105,110,118,101,114,115,101,32,61,61,32,48,0,0,0,0,100,115,102,91,118,49,93,32,38,32,50,0,0,0,0,0,101,100,115,102,95,109,101,114,103,101,0,0,0,0,0,0,100,115,102,91,118,50,93,32,38,32,50,0,0,0,0,0,33,105,110,118,101,114,115,101,0,0,0,0,0,0,0,0,105,110,118,101,114,115,101,32,61,61,32,48,32,124,124,32,105,110,118,101,114,115,101,32,61,61,32,49,0,0,0,0,118,50,32,61,61,32,118,49,0,0,0,0,0,0,0,0,105,50,32,61,61,32,105,110,118,101,114,115,101,0,0,0,112,117,122,122,108,101,32,102,97,116,97,108,32,101,114,114,111,114,58,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,66,97,99,107,115,112,97,99,101,0,0,0,0,0,0,0,68,101,108,0,0,0,0,0,69,110,116,101,114,0,0,0,76,101,102,116,0,0,0,0,85,112,0,0,0,0,0,0,82,105,103,104,116,0,0,0,68,111,119,110,0,0,0,0,69,110,100,0,0,0,0,0,80,97,103,101,68,111,119,110,0,0,0,0,0,0,0,0,72,111,109,101,0,0,0,0,80,97,103,101,85,112,0,0,1,0,0,0,1,0,0,0,2,0,0,0,1,0,0,0,3,0,0,0,2,0,0,0,3,0,0,0,1,0,0,0,2,0,0,0,3,0,0,0,1,0,0,0,1,0,0,0,2,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,105,32,60,32,110,112,114,101,115,101,116,115,0,0,0,0,101,109,99,99,46,99,0,0,99,111,109,109,97,110,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,35,37,48,50,120,37,48,50,120,37,48,50,120,0,0,0,0,0,0,0,0,0,0,0,37,100,112,120,32,37,115,0,109,111,110,111,115,112,97,99,101,0,0,0,0,0,0,0,115,97,110,115,45,115,101,114,105,102,0,0,0,0,0,0,111,117,116,32,111,102,32,109,101,109,111,114,121,0,0,0,37,115,95,84,73,76,69,83,73,90,69,0,0,0,0,0,37,100,0,0,0,0,0,0,37,115,95,68,69,70,65,85,76,84,0,0,0,0,0,0,109,101,45,62,110,115,116,97,116,101,115,32,61,61,32,48,0,0,0,0,0,0,0,0,109,105,100,101,110,100,46,99,0,0,0,0,0,0,0,0,109,105,100,101,110,100,95,110,101,119,95,103,97,109,101,0,109,111,118,101,115,116,114,32,38,38,32,33,109,115,103,0,115,0,0,0,0,0,0,0,109,101,45,62,115,116,97,116,101,112,111,115,32,62,61,32,49,0,0,0,0,0,0,0,109,105,100,101,110,100,95,114,101,115,116,97,114,116,95,103,97,109,101,0,0,0,0,0,109,101,45,62,100,114,97,119,105,110,103,0,0,0,0,0,109,105,100,101,110,100,95,114,101,100,114,97,119,0,0,0,109,101,45,62,100,105,114,32,33,61,32,48,0,0,0,0,0,0,0,0,0,0,0,0,37,115,95,67,79,76,79,85,82,95,37,100,0,0,0,0,37,50,120,37,50,120,37,50,120,0,0,0,0,0,0,0,37,115,95,80,82,69,83,69,84,83,0,0,0,0,0,0,110,32,62,61,32,48,32,38,38,32,110,32,60,32,109,101,45,62,110,112,114,101,115,101,116,115,0,0,0,0,0,0,109,105,100,101,110,100,95,102,101,116,99,104,95,112,114,101,115,101,116,0,0,0,0,0,119,105,110,116,105,116,108,101,0,0,0,0,0,0,0,0,109,105,100,101,110,100,95,103,101,116,95,99,111,110,102,105,103,0,0,0,0,0,0,0,37,115,32,99,111,110,102,105,103,117,114,97,116,105,111,110,0,0,0,0,0,0,0,0,37,115,32,37,115,32,115,101,108,101,99,116,105,111,110,0,114,97,110,100,111,109,0,0,103,97,109,101,0,0,0,0,71,97,109,101,32,114,97,110,100,111,109,32,115,101,101,100,0,0,0,0,0,0,0,0,71,97,109,101,32,73,68,0,112,97,114,115,116,114,0,0,37,115,37,99,37,115,0,0,33,34,87,101,32,115,104,111,117,108,100,110,39,116,32,98,101,32,104,101,114,101,34,0,109,105,100,101,110,100,95,103,101,116,95,103,97,109,101,95,105,100,0,0,0,0,0,0,109,101,45,62,100,101,115,99,0,0,0,0,0,0,0,0,37,115,58,37,115,0,0,0,109,105,100,101,110,100,95,103,101,116,95,114,97,110,100,111,109,95,115,101,101,100,0,0,37,115,35,37,115,0,0,0,84,104,105,115,32,103,97,109,101,32,100,111,101,115,32,110,111,116,32,115,117,112,112,111,114,116,32,116,104,101,32,83,111,108,118,101,32,111,112,101,114,97,116,105,111,110,0,0,78,111,32,103,97,109,101,32,115,101,116,32,117,112,32,116,111,32,115,111,108,118,101,0,83,111,108,118,101,32,111,112,101,114,97,116,105,111,110,32,102,97,105,108,101,100,0,0,109,105,100,101,110,100,95,115,111,108,118,101,0,0,0,0,91,37,100,58,37,48,50,100,93,32,0,0,0,0,0,0,115,32,33,61,32,78,85,76,76,0,0,0,0,0,0,0,109,105,100,101,110,100,95,114,101,97,108,108,121,95,112,114,111,99,101,115,115,95,107,101,121,0,0,0,0,0,0,0,109,111,118,101,115,116,114,32,33,61,32,78,85,76,76,0,98,105,116,115,32,60,32,51,50,0,0,0,0,0,0,0,114,97,110,100,111,109,46,99,0,0,0,0,0,0,0,0,114,97,110,100,111,109,95,117,112,116,111,0,0,0,0,0,83,111,108,111,0,0,0,0,103,97,109,101,115,46,115,111,108,111,0,0,0,0,0,0,115,111,108,111,0,0,0,0,104,6,0,0,112,6,0,0,128,6,0,0,1,0,0,0,3,0,0,0,3,0,0,0,1,0,0,0,4,0,0,0,1,0,0,0,1,0,0,0,2,0,0,0,3,0,0,0,2,0,0,0,1,0,0,0,3,0,0,0,4,0,0,0,4,0,0,0,5,0,0,0,1,0,0,0,2,0,0,0,1,0,0,0,5,0,0,0,6,0,0,0,7,0,0,0,6,0,0,0,8,0,0,0,4,0,0,0,1,0,0,0,1,0,0,0,4,0,0,0,48,0,0,0,3,0,0,0,4,0,0,0,5,0,0,0,6,0,0,0,5,0,0,0,1,0,0,0,1,0,0,0,2,0,0,0,9,0,0,0,1,0,0,0,0,0,0,0,2,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,0,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,37,100,0,0,0,0,0,0,105,32,60,32,99,114,0,0,115,111,108,111,46,99,0,0,111,117,116,108,105,110,101,95,98,108,111,99,107,95,115,116,114,117,99,116,117,114,101,0,120,32,62,61,32,48,32,38,38,32,120,32,60,32,99,114,32,38,38,32,121,32,62,61,32,48,32,38,38,32,121,32,60,32,99,114,32,38,38,32,98,108,111,99,107,115,45,62,119,104,105,99,104,98,108,111,99,107,91,121,42,99,114,43,120,93,32,61,61,32,98,105,0,0,0,0,0,0,0,0,120,43,100,120,32,60,32,48,32,124,124,32,120,43,100,120,32,62,61,32,99,114,32,124,124,32,121,43,100,121,32,60,32,48,32,124,124,32,121,43,100,121,32,62,61,32,99,114,32,124,124,32,98,108,111,99,107,115,45,62,119,104,105,99,104,98,108,111,99,107,91,40,121,43,100,121,41,42,99,114,43,40,120,43,100,120,41,93,32,33,61,32,98,105,0,0,110,32,60,32,50,42,99,114,43,50,0,0,0,0,0,0,99,108,117,101,32,61,61,32,48,0,0,0,0,0,0,0,103,97,109,101,95,114,101,100,114,97,119,0,0,0,0,0,99,108,117,101,32,33,61,32,48,0,0,0,0,0,0,0,112,98,101,115,116,32,62,32,48,0,0,0,0,0,0,0,100,114,97,119,95,110,117,109,98,101,114,0,0,0,0,0,37,100,44,37,100,44,37,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,37,99,37,100,44,37,100,44,37,100,0,0,0,0,0,0,77,0,0,0,0,0,0,0,33,115,116,97,116,101,45,62,107,98,108,111,99,107,115,0,103,97,109,101,95,116,101,120,116,95,102,111,114,109,97,116,0,0,0,0,0,0,0,0,112,32,45,32,114,101,116,32,61,61,32,116,111,116,97,108,108,101,110,0,0,0,0,0,103,114,105,100,95,116,101,120,116,95,102,111,114,109,97,116,0,0,0,0,0,0,0,0,78,111,32,115,111,108,117,116,105,111,110,32,101,120,105,115,116,115,32,102,111,114,32,116,104,105,115,32,112,117,122,122,108,101,0,0,0,0,0,0,77,117,108,116,105,112,108,101,32,115,111,108,117,116,105,111,110,115,32,101,120,105,115,116,32,102,111,114,32,116,104,105,115,32,112,117,122,122,108,101,0,0,0,0,0,0,0,0,37,115,37,100,0,0,0,0,44,0,0,0,0,0,0,0,112,32,45,32,114,101,116,32,61,61,32,108,101,110,0,0,101,110,99,111,100,101,95,115,111,108,118,101,95,109,111,118,101,0,0,0,0,0,0,0,107,98,108,111,99,107,115,0,115,111,108,118,101,114,0,0,117,115,97,103,101,45,62,107,99,108,117,101,115,91,105,93,32,62,32,48,0,0,0,0,115,117,109,32,62,32,48,0,117,115,97,103,101,45,62,107,98,108,111,99,107,115,45,62,110,114,95,115,113,117,97,114,101,115,91,98,93,32,62,32,110,115,113,117,97,114,101,115,0,0,0,0,0,0,0,0,117,115,97,103,101,45,62,107,98,108,111,99,107,115,45,62,110,114,95,115,113,117,97,114,101,115,91,117,115,97,103,101,45,62,107,98,108,111,99,107,115,45,62,110,114,95,98,108,111,99,107,115,32,45,32,49,93,32,61,61,32,110,115,113,117,97,114,101,115,0,0,0,99,111,117,110,116,32,62,32,49,0,0,0,0,0,0,0,99,111,117,110,116,32,62,32,48,0,0,0,0,0,0,0,115,111,108,118,101,114,95,115,101,116,0,0,0,0,0,0,110,32,61,61,32,106,0,0,110,115,113,117,97,114,101,115,32,61,61,32,48,0,0,0,115,111,108,118,101,114,95,107,105,108,108,101,114,95,115,117,109,115,0,0,0,0,0,0,110,115,113,117,97,114,101,115,32,62,32,48,0,0,0,0,117,115,97,103,101,45,62,103,114,105,100,91,120,93,32,61,61,32,48,0,0,0,0,0,98,45,62,109,97,120,95,110,114,95,115,113,117,97,114,101,115,32,62,61,32,110,114,95,115,113,117,97,114,101,115,0,115,112,108,105,116,95,98,108,111,99,107,0,0,0,0,0,98,45,62,110,114,95,115,113,117,97,114,101,115,91,112,114,101,118,105,111,117,115,95,98,108,111,99,107,93,32,62,32,110,114,95,115,113,117,97,114,101,115,0,0,0,0,0,0,98,45,62,119,104,105,99,104,98,108,111,99,107,91,115,113,117,97,114,101,115,91,105,93,93,32,61,61,32,112,114,101,118,105,111,117,115,95,98,108,111,99,107,0,0,0,0,0,111,102,102,32,61,61,32,110,0,0,0,0,0,0,0,0,102,105,108,116,101,114,95,119,104,111,108,101,95,99,97,103,101,115,0,0,0,0,0,0,106,43,49,32,61,61,32,105,0,0,0,0,0,0,0,0,114,101,109,111,118,101,95,102,114,111,109,95,98,108,111,99,107,0,0,0,0,0,0,0,102,112,111,115,32,62,61,32,48,0,0,0,0,0,0,0,115,111,108,118,101,114,95,101,108,105,109,0,0,0,0,0,99,117,98,101,40,120,44,121,44,110,41,0,0,0,0,0,115,111,108,118,101,114,95,112,108,97,99,101,0,0,0,0,42,100,101,115,99,32,61,61,32,39,44,39,0,0,0,0,110,101,119,95,103,97,109,101,0,0,0,0,0,0,0,0,101,114,114,32,61,61,32,78,85,76,76,0,0,0,0,0,33,42,100,101,115,99,0,0,106,32,60,32,98,108,111,99,107,115,45,62,109,97,120,95,110,114,95,115,113,117,97,114,101,115,0,0,0,0,0,0,109,97,107,101,95,98,108,111,99,107,115,95,102,114,111,109,95,119,104,105,99,104,98,108,111,99,107,0,0,0,0,0,110,98,32,62,61,32,109,105,110,95,101,120,112,101,99,116,101,100,32,38,38,32,110,98,32,60,61,32,109,97,120,95,101,120,112,101,99,116,101,100,0,0,0,0,0,0,0,0,100,115,102,95,116,111,95,98,108,111,99,107,115,0,0,0,73,110,118,97,108,105,100,32,99,104,97,114,97,99,116,101,114,32,105,110,32,103,97,109,101,32,100,101,115,99,114,105,112,116,105,111,110,0,0,0,84,111,111,32,109,117,99,104,32,100,97,116,97,32,105,110,32,98,108,111,99,107,32,115,116,114,117,99,116,117,114,101,32,115,112,101,99,105,102,105,99,97,116,105,111,110,0,0,78,111,116,32,101,110,111,117,103,104,32,100,97,116,97,32,105,110,32,98,108,111,99,107,32,115,116,114,117,99,116,117,114,101,32,115,112,101,99,105,102,105,99,97,116,105,111,110,0,0,0,0,0,0,0,0,105,32,43,32,114,117,110,32,60,61,32,97,114,101,97,0,115,112,101,99,95,116,111,95,103,114,105,100,0,0,0,0,105,32,60,32,97,114,101,97,0,0,0,0,0,0,0,0,33,34,87,101,32,99,97,110,39,116,32,103,101,116,32,104,101,114,101,34,0,0,0,0,105,32,61,61,32,97,114,101,97,0,0,0,0,0,0,0,106,32,60,61,32,77,65,88,95,50,83,85,77,83,0,0,112,114,101,99,111,109,112,117,116,101,95,115,117,109,95,98,105,116,115,0,0,0,0,0,106,32,60,61,32,77,65,88,95,51,83,85,77,83,0,0,106,32,60,61,32,77,65,88,95,52,83,85,77,83,0,0,97,100,100,101,110,100,115,95,108,101,102,116,32,62,61,32,50,0,0,0,0,0,0,0,102,105,110,100,95,115,117,109,95,98,105,116,115,0,0,0,98,105,116,109,97,115,107,95,115,111,95,102,97,114,32,33,61,32,110,101,119,95,98,105,116,109,97,115,107,0,0,0,69,120,112,101,99,116,101,100,32,106,105,103,115,97,119,32,98,108,111,99,107,32,115,116,114,117,99,116,117,114,101,32,105,110,32,103,97,109,101,32,100,101,115,99,114,105,112,116,105,111,110,0,0,0,0,0,69,120,112,101,99,116,101,100,32,107,105,108,108,101,114,32,98,108,111,99,107,32,115,116,114,117,99,116,117,114,101,32,105,110,32,103,97,109,101,32,100,101,115,99,114,105,112,116,105,111,110,0,0,0,0,0,69,120,112,101,99,116,101,100,32,107,105,108,108,101,114,32,99,108,117,101,32,103,114,105,100,32,105,110,32,103,97,109,101,32,100,101,115,99,114,105,112,116,105,111,110,0,0,0,85,110,101,120,112,101,99,116,101,100,32,100,97,116,97,32,97,116,32,101,110,100,32,111,102,32,103,97,109,101,32,100,101,115,99,114,105,112,116,105,111,110,0,0,0,0,0,0,109,105,110,95,110,114,95,98,108,111,99,107,115,32,61,61,32,109,97,120,95,110,114,95,98,108,111,99,107,115,0,0,118,97,108,105,100,97,116,101,95,98,108,111,99,107,95,100,101,115,99,0,0,0,0,0,109,105,110,95,110,114,95,98,108,111,99,107,115,32,42,32,109,105,110,95,110,114,95,115,113,117,97,114,101,115,32,61,61,32,97,114,101,97,0,0,65,32,106,105,103,115,97,119,32,98,108,111,99,107,32,105,115,32,116,111,111,32,98,105,103,0,0,0,0,0,0,0,84,111,111,32,109,97,110,121,32,100,105,115,116,105,110,99,116,32,106,105,103,115,97,119,32,98,108,111,99,107,115,0,78,111,116,32,101,110,111,117,103,104,32,100,105,115,116,105,110,99,116,32,106,105,103,115,97,119,32,98,108,111,99,107,115,0,0,0,0,0,0,0,65,32,106,105,103,115,97,119,32,98,108,111,99,107,32,105,115,32,116,111,111,32,115,109,97,108,108,0,0,0,0,0,79,117,116,45,111,102,45,114,97,110,103,101,32,110,117,109,98,101,114,32,105,110,32,103,97,109,101,32,100,101,115,99,114,105,112,116,105,111,110,0,78,111,116,32,101,110,111,117,103,104,32,100,97,116,97,32,116,111,32,102,105,108,108,32,103,114,105,100,0,0,0,0,84,111,111,32,109,117,99,104,32,100,97,116,97,32,116,111,32,102,105,116,32,105,110,32,103,114,105,100,0,0,0,0,99,104,101,99,107,95,118,97,108,105,100,40,99,114,44,32,98,108,111,99,107,115,44,32,107,98,108,111,99,107,115,44,32,112,97,114,97,109,115,45,62,120,116,121,112,101,44,32,103,114,105,100,41,0,0,0,110,101,119,95,103,97,109,101,95,100,101,115,99,0,0,0,112,32,45,32,100,101,115,99,32,60,32,115,112,97,99,101,0,0,0,0,0,0,0,0,101,110,99,111,100,101,95,112,117,122,122,108,101,95,100,101,115,99,0,0,0,0,0,0,106,32,33,61,32,97,114,101,97,0,0,0,0,0,0,0,99,111,109,112,117,116,101,95,107,99,108,117,101,115,0,0,121,32,61,61,32,110,95,115,105,110,103,108,101,116,111,110,115,0,0,0,0,0,0,0,103,101,110,95,107,105,108,108,101,114,95,99,97,103,101,115,0,0,0,0,0,0,0,0,110,95,115,105,110,103,108,101,116,111,110,115,32,61,61,32,48,0,0,0,0,0,0,0,66,111,116,104,32,100,105,109,101,110,115,105,111,110,115,32,109,117,115,116,32,98,101,32,97,116,32,108,101,97,115,116,32,50,0,0,0,0,0,0,68,105,109,101,110,115,105,111,110,115,32,103,114,101,97,116,101,114,32,116,104,97,110,32,50,53,53,32,97,114,101,32,110,111,116,32,115,117,112,112,111,114,116,101,100,0,0,0,85,110,97,98,108,101,32,116,111,32,115,117,112,112,111,114,116,32,109,111,114,101,32,116,104,97,110,32,51,49,32,100,105,115,116,105,110,99,116,32,115,121,109,98,111,108,115,32,105,110,32,97,32,112,117,122,122,108,101,0,0,0,0,0,75,105,108,108,101,114,32,112,117,122,122,108,101,32,100,105,109,101,110,115,105,111,110,115,32,109,117,115,116,32,98,101,32,115,109,97,108,108,101,114,32,116,104,97,110,32,49,48,46,0,0,0,0,0,0,0,67,111,108,117,109,110,115,32,111,102,32,115,117,98,45,98,108,111,99,107,115,0,0,0,82,111,119,115,32,111,102,32,115,117,98,45,98,108,111,99,107,115,0,0,0,0,0,0,34,88,34,32,40,114,101,113,117,105,114,101,32,101,118,101,114,121,32,110,117,109,98,101,114,32,105,110,32,101,97,99,104,32,109,97,105,110,32,100,105,97,103,111,110,97,108,41,0,0,0,0,0,0,0,0,74,105,103,115,97,119,32,40,105,114,114,101,103,117,108,97,114,108,121,32,115,104,97,112,101,100,32,115,117,98,45,98,108,111,99,107,115,41,0,0,75,105,108,108,101,114,32,40,100,105,103,105,116,32,115,117,109,115,41,0,0,0,0,0,83,121,109,109,101,116,114,121,0,0,0,0,0,0,0,0,58,78,111,110,101,58,50,45,119,97,121,32,114,111,116,97,116,105,111,110,58,52,45,119,97,121,32,114,111,116,97,116,105,111,110,58,50,45,119,97,121,32,109,105,114,114,111,114,58,50,45,119,97,121,32,100,105,97,103,111,110,97,108,32,109,105,114,114,111,114,58,52,45,119,97,121,32,109,105,114,114,111,114,58,52,45,119,97,121,32,100,105,97,103,111,110,97,108,32,109,105,114,114,111,114,58,56,45,119,97,121,32,109,105,114,114,111,114,0,0,68,105,102,102,105,99,117,108,116,121,0,0,0,0,0,0,58,84,114,105,118,105,97,108,58,66,97,115,105,99,58,73,110,116,101,114,109,101,100,105,97,116,101,58,65,100,118,97,110,99,101,100,58,69,120,116,114,101,109,101,58,85,110,114,101,97,115,111,110,97,98,108,101,0,0,0,0,0,0,0,37,100,120,37,100,0,0,0,37,100,106,0,0,0,0,0,120,0,0,0,0,0,0,0,107,0,0,0,0,0,0,0,109,56,0,0,0,0,0,0,109,52,0,0,0,0,0,0,109,100,52,0,0,0,0,0,109,50,0,0,0,0,0,0,109,100,50,0,0,0,0,0,114,52,0,0,0,0,0,0,97,0,0,0,0,0,0,0,100,98,0,0,0,0,0,0,100,105,0,0,0,0,0,0,100,97,0,0,0,0,0,0,100,101,0,0,0,0,0,0,100,117,0,0,0,0,0,0,8,32,0,0,2,0,0,0,2,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,24,32,0,0,2,0,0,0,3,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,40,32,0,0,3,0,0,0,3,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,56,32,0,0,3,0,0,0,3,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,72,32,0,0,3,0,0,0,3,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,88,32,0,0,3,0,0,0,3,0,0,0,1,0,0,0,2,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,112,32,0,0,3,0,0,0,3,0,0,0,1,0,0,0,3,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,128,32,0,0,3,0,0,0,3,0,0,0,1,0,0,0,3,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,144,32,0,0,3,0,0,0,3,0,0,0,1,0,0,0,4,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,160,32,0,0,3,0,0,0,3,0,0,0,1,0,0,0,5,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,184,32,0,0,3,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,1,0,0,0,200,32,0,0,9,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,216,32,0,0,9,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,240,32,0,0,9,0,0,0,1,0,0,0,1,0,0,0,3,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,50,120,50,32,84,114,105,118,105,97,108,0,0,0,0,0,50,120,51,32,66,97,115,105,99,0,0,0,0,0,0,0,51,120,51,32,84,114,105,118,105,97,108,0,0,0,0,0,51,120,51,32,66,97,115,105,99,0,0,0,0,0,0,0,51,120,51,32,66,97,115,105,99,32,88,0,0,0,0,0,51,120,51,32,73,110,116,101,114,109,101,100,105,97,116,101,0,0,0,0,0,0,0,0,51,120,51,32,65,100,118,97,110,99,101,100,0,0,0,0,51,120,51,32,65,100,118,97,110,99,101,100,32,88,0,0,51,120,51,32,69,120,116,114,101,109,101,0,0,0,0,0,51,120,51,32,85,110,114,101,97,115,111,110,97,98,108,101,0,0,0,0,0,0,0,0,51,120,51,32,75,105,108,108,101,114,0,0,0,0,0,0,57,32,74,105,103,115,97,119,32,66,97,115,105,99,0,0,57,32,74,105,103,115,97,119,32,66,97,115,105,99,32,88,0,0,0,0,0,0,0,0,57,32,74,105,103,115,97,119,32,65,100,118,97,110,99,101,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], "i8", ALLOC_NONE, Runtime.GLOBAL_BASE);




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

  function _js_canvas_free_blitter(id) {
          blitters[id] = null;
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

  function _js_canvas_start_draw() {
          ctx = offscreen_canvas.getContext('2d');
          update_xmin = update_xmax = update_ymin = update_ymax = undefined;
      }

  function _js_enable_undo_redo(undo, redo) {
          undo_button.disabled = (undo == 0);
          redo_button.disabled = (redo == 0);
      }

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
          canvas.style.backgroundColor = "black";

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

  function _isspace(chr) {
      return (chr == 32) || (chr >= 9 && chr <= 13);
    }

  function _js_dialog_init(titletext) {
          // Create an overlay on the page which darkens everything
          // beneath it.
          dlg_dimmer = document.createElement("div");
          dlg_dimmer.style.width = "100%";
          dlg_dimmer.style.height = "100%";
          dlg_dimmer.style.background = '#000000';
          dlg_dimmer.style.position = 'fixed';
          dlg_dimmer.style.opacity = 0.3;
          dlg_dimmer.style.top = dlg_dimmer.style.left = 0;
          dlg_dimmer.style["z-index"] = 99;

          // Now create a form which sits on top of that in turn.
          dlg_form = document.createElement("form");
          dlg_form.style.width = (window.innerWidth * 2 / 3) + "px";
          dlg_form.style.opacity = 1;
          dlg_form.style.background = '#ffffff';
          dlg_form.style.color = '#000000';
          dlg_form.style.position = 'absolute';
          dlg_form.style.border = "2px solid black";
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

  function _js_canvas_make_statusbar() {
          var statusholder = document.getElementById("statusbarholder");
          statusbar = document.createElement("div");
          statusbar.style.overflow = "hidden";
          statusbar.style.width = (onscreen_canvas.width - 4) + "px";
          statusholder.style.width = onscreen_canvas.width + "px";
          statusbar.style.height = "1.2em";
          statusbar.style.textAlign = "left";
          statusbar.style.background = "#d8d8d8";
          statusbar.style.borderLeft = '2px solid #c8c8c8';
          statusbar.style.borderTop = '2px solid #c8c8c8';
          statusbar.style.borderRight = '2px solid #e8e8e8';
          statusbar.style.borderBottom = '2px solid #e8e8e8';
          statusbar.appendChild(document.createTextNode(" "));
          statusholder.appendChild(statusbar);
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

  function _js_canvas_draw_rect(x, y, w, h, colptr) {)
          if (colptr == "5262592") {
            ctx.fillStyle = "#fff";
          } else {
            ctx.fillStyle = Pointer_stringify(colptr);
          }
          ctx.fillRect(x, y, w, h);
      }

  function _js_deactivate_timer() {
          if (timer !== null) {
              clearInterval(timer);
              timer = null;
          }
      }

  function _js_focus_canvas() {
          onscreen_canvas.focus();
      }

  function _js_canvas_draw_line(x1, y1, x2, y2, width, colour) {
          colour = Pointer_stringify(colour);

          ctx.beginPath();
          ctx.moveTo(x1 + 0.5, y1 + 0.5);
          ctx.lineTo(x2 + 0.5, y2 + 0.5);
          ctx.lineWidth = width;
          ctx.lineCap = 'round';
          ctx.lineJoin = 'round';
          ctx.strokeStyle = colour;
          ctx.stroke();
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


  Module["_memmove"] = _memmove;

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
          ctx2.fillStyle = "#000000";
          ctx2.fillRect(0, 0, width, 2*height);
          var baseline = (1.5*height) | 0;
          ctx2.fillStyle = "#ffffff";
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

  function _js_remove_solve_button() {
          document.getElementById("solve").style.display = "none";
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


  Module["_strcpy"] = _strcpy;

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

function invoke_vid(index,a1,a2) {
  try {
    Module["dynCall_vid"](index,a1,a2);
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
var asm=(function(global,env,buffer){"use asm";var a=new global.Int8Array(buffer);var b=new global.Int16Array(buffer);var c=new global.Int32Array(buffer);var d=new global.Uint8Array(buffer);var e=new global.Uint16Array(buffer);var f=new global.Uint32Array(buffer);var g=new global.Float32Array(buffer);var h=new global.Float64Array(buffer);var i=env.STACKTOP|0;var j=env.STACK_MAX|0;var k=env.tempDoublePtr|0;var l=env.ABORT|0;var m=0;var n=0;var o=0;var p=0;var q=+env.NaN,r=+env.Infinity;var s=0,t=0,u=0,v=0,w=0.0,x=0,y=0,z=0,A=0.0;var B=0;var C=0;var D=0;var E=0;var F=0;var G=0;var H=0;var I=0;var J=0;var K=0;var L=global.Math.floor;var M=global.Math.abs;var N=global.Math.sqrt;var O=global.Math.pow;var P=global.Math.cos;var Q=global.Math.sin;var R=global.Math.tan;var S=global.Math.acos;var T=global.Math.asin;var U=global.Math.atan;var V=global.Math.atan2;var W=global.Math.exp;var X=global.Math.log;var Y=global.Math.ceil;var Z=global.Math.imul;var _=env.abort;var $=env.assert;var aa=env.asmPrintInt;var ba=env.asmPrintFloat;var ca=env.min;var da=env.invoke_iiiii;var ea=env.invoke_vid;var fa=env.invoke_viiiii;var ga=env.invoke_i;var ha=env.invoke_vi;var ia=env.invoke_vii;var ja=env.invoke_iiiiiii;var ka=env.invoke_vidddddi;var la=env.invoke_viiiiiidd;var ma=env.invoke_ii;var na=env.invoke_iiii;var oa=env.invoke_viii;var pa=env.invoke_viiiiiiii;var qa=env.invoke_viiiiii;var ra=env.invoke_iii;var sa=env.invoke_diiii;var ta=env.invoke_viiii;var ua=env._js_error_box;var va=env._js_dialog_cleanup;var wa=env._js_select_preset;var xa=env._js_dialog_init;var ya=env._js_canvas_draw_line;var za=env.___setErrNo;var Aa=env._js_canvas_find_font_midpoint;var Ba=env.___assert_fail;var Ca=env.___buildEnvironment;var Da=env._js_focus_canvas;var Ea=env._js_canvas_set_size;var Fa=env._js_dialog_launch;var Ga=env._js_canvas_draw_circle;var Ha=env._js_canvas_draw_rect;var Ia=env._sscanf;var Ja=env._sbrk;var Ka=env._js_dialog_boolean;var La=env._js_canvas_new_blitter;var Ma=env._snprintf;var Na=env.___errno_location;var Oa=env._emscripten_memcpy_big;var Pa=env._js_canvas_make_statusbar;var Qa=env._js_enable_undo_redo;var Ra=env._sysconf;var Sa=env._js_canvas_unclip;var Ta=env._js_canvas_draw_poly;var Ua=env._js_canvas_draw_text;var Va=env._js_dialog_string;var Wa=env._js_canvas_draw_update;var Xa=env._js_update_permalinks;var Ya=env._isspace;var Za=env._js_remove_type_dropdown;var _a=env._js_remove_solve_button;var $a=env._getenv;var ab=env._sprintf;var bb=env._js_canvas_start_draw;var cb=env.__reallyNegative;var db=env._toupper;var eb=env._js_get_date_64;var fb=env._fflush;var gb=env.__scanString;var hb=env._js_deactivate_timer;var ib=env._vsnprintf;var jb=env._js_canvas_copy_from_blitter;var kb=env._js_activate_timer;var lb=env._js_canvas_end_draw;var mb=env._js_canvas_free_blitter;var nb=env._abort;var ob=env._js_dialog_choices;var pb=env._js_canvas_copy_to_blitter;var qb=env._time;var rb=env._isdigit;var sb=env._js_canvas_set_statusbar;var tb=env._js_add_preset;var ub=env.__formatString;var vb=env._js_canvas_clip_rect;var wb=env._sqrt;var xb=env.__getFloat;var yb=env._js_get_selected_preset;var zb=0.0;
// EMSCRIPTEN_START_FUNCS
function Rb(a){a=a|0;var b=0;b=i;i=i+a|0;i=i+7&-8;return b|0}function Sb(){return i|0}function Tb(a){a=a|0;i=a}function Ub(a,b){a=a|0;b=b|0;if((m|0)==0){m=a;n=b}}function Vb(b){b=b|0;a[k]=a[b];a[k+1|0]=a[b+1|0];a[k+2|0]=a[b+2|0];a[k+3|0]=a[b+3|0]}function Wb(b){b=b|0;a[k]=a[b];a[k+1|0]=a[b+1|0];a[k+2|0]=a[b+2|0];a[k+3|0]=a[b+3|0];a[k+4|0]=a[b+4|0];a[k+5|0]=a[b+5|0];a[k+6|0]=a[b+6|0];a[k+7|0]=a[b+7|0]}function Xb(a){a=a|0;B=a}function Yb(a){a=a|0;C=a}function Zb(a){a=a|0;D=a}function _b(a){a=a|0;E=a}function $b(a){a=a|0;F=a}function ac(a){a=a|0;G=a}function bc(a){a=a|0;H=a}function cc(a){a=a|0;I=a}function dc(a){a=a|0;J=a}function ec(a){a=a|0;K=a}function fc(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0;f=i;i=i+32|0;g=f+16|0;h=f+12|0;j=f+8|0;k=f+4|0;l=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;do{c[l>>2]=gc(c[g>>2]|0,c[h>>2]|0,c[j>>2]|0,c[k>>2]|0)|0}while((c[l>>2]|0)!=0^1);i=f;return c[l>>2]|0}function gc(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0,L=0,M=0,N=0,O=0,P=0,Q=0,R=0,S=0,T=0,U=0,V=0,W=0,X=0,Y=0,_=0,$=0;f=i;i=i+128|0;g=f+124|0;h=f+120|0;j=f+116|0;k=f+112|0;l=f+108|0;m=f+104|0;n=f+100|0;o=f+96|0;p=f+92|0;q=f+88|0;r=f+84|0;s=f+80|0;t=f+76|0;u=f+72|0;v=f+68|0;w=f+64|0;x=f+60|0;y=f+56|0;z=f+52|0;A=f+48|0;B=f+44|0;C=f+40|0;D=f+36|0;E=f+32|0;F=f+28|0;G=f+24|0;H=f+20|0;I=f+16|0;J=f+12|0;K=f+8|0;L=f+4|0;M=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[t>>2]=Z(c[g>>2]|0,c[h>>2]|0)|0;c[w>>2]=(c[t>>2]|0)/(c[j>>2]|0)|0;if((c[t>>2]|0)!=(Z(c[j>>2]|0,c[w>>2]|0)|0)){Ba(8,24,270,32)}c[l>>2]=sd(c[t>>2]<<2)|0;c[n>>2]=sd(c[t>>2]<<2)|0;c[o>>2]=sd(c[t>>2]<<2)|0;c[p>>2]=sd(c[w>>2]<<2)|0;c[m>>2]=sd(c[w>>2]<<2)|0;c[q>>2]=sd(c[t>>2]<<2<<2)|0;c[r>>2]=sd(c[t>>2]<<2)|0;c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[t>>2]|0)){break}c[(c[l>>2]|0)+(c[u>>2]<<2)>>2]=c[u>>2];c[u>>2]=(c[u>>2]|0)+1}ee(c[l>>2]|0,c[t>>2]|0,4,c[k>>2]|0);c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[t>>2]|0)){break}c[(c[o>>2]|0)+(c[u>>2]<<2)>>2]=-1;c[u>>2]=(c[u>>2]|0)+1}c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[w>>2]|0)){break}c[(c[o>>2]|0)+(c[(c[l>>2]|0)+(c[u>>2]<<2)>>2]<<2)>>2]=c[u>>2];c[(c[p>>2]|0)+(c[u>>2]<<2)>>2]=1;c[u>>2]=(c[u>>2]|0)+1}a:while(1){c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[h>>2]|0)){break}c[x>>2]=0;while(1){N=c[y>>2]|0;if((c[x>>2]|0)>=(c[g>>2]|0)){break}e=Z(N,c[g>>2]|0)|0;c[B>>2]=e+(c[x>>2]|0);c[C>>2]=c[(c[o>>2]|0)+(c[B>>2]<<2)>>2];do{if((c[C>>2]|0)>=0){if((c[(c[p>>2]|0)+(c[C>>2]<<2)>>2]|0)==1){c[(c[r>>2]|0)+(c[B>>2]<<2)>>2]=1;break}else{e=hc(c[g>>2]|0,c[h>>2]|0,c[x>>2]|0,c[y>>2]|0,c[o>>2]|0,c[C>>2]|0)|0;c[(c[r>>2]|0)+(c[B>>2]<<2)>>2]=e;break}}else{c[(c[r>>2]|0)+(c[B>>2]<<2)>>2]=0}}while(0);c[D>>2]=0;while(1){if((c[D>>2]|0)>=4){break}if((c[D>>2]|0)==0){O=-1}else{O=(c[D>>2]|0)==1?1:0}c[E>>2]=O;if((c[D>>2]|0)==2){P=-1}else{P=(c[D>>2]|0)==3?1:0}c[F>>2]=P;c[G>>2]=(c[x>>2]|0)+(c[E>>2]|0);c[H>>2]=(c[y>>2]|0)+(c[F>>2]|0);e=Z(c[H>>2]|0,c[g>>2]|0)|0;c[I>>2]=e+(c[G>>2]|0);c[(c[q>>2]|0)+((c[B>>2]<<2)+(c[D>>2]|0)<<2)>>2]=-1;if(((((((c[G>>2]|0)>=0?(c[G>>2]|0)<(c[g>>2]|0):0)?(c[H>>2]|0)>=0:0)?(c[H>>2]|0)<(c[h>>2]|0):0)?(c[(c[o>>2]|0)+(c[I>>2]<<2)>>2]|0)>=0:0)?(c[(c[o>>2]|0)+(c[I>>2]<<2)>>2]|0)!=(c[(c[o>>2]|0)+(c[B>>2]<<2)>>2]|0):0)?(hc(c[g>>2]|0,c[h>>2]|0,c[x>>2]|0,c[y>>2]|0,c[o>>2]|0,c[(c[o>>2]|0)+(c[I>>2]<<2)>>2]|0)|0)!=0:0){c[(c[q>>2]|0)+((c[B>>2]<<2)+(c[D>>2]|0)<<2)>>2]=c[(c[o>>2]|0)+(c[I>>2]<<2)>>2]}c[D>>2]=(c[D>>2]|0)+1}c[x>>2]=(c[x>>2]|0)+1}c[y>>2]=N+1}c[v>>2]=0;c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[w>>2]|0)){break}if((c[(c[p>>2]|0)+(c[u>>2]<<2)>>2]|0)<(c[j>>2]|0)){e=c[u>>2]|0;d=c[v>>2]|0;c[v>>2]=d+1;c[(c[n>>2]|0)+(d<<2)>>2]=e}c[u>>2]=(c[u>>2]|0)+1}if((c[v>>2]|0)==0){Q=92;break}e=qe(c[k>>2]|0,c[v>>2]|0)|0;c[v>>2]=c[(c[n>>2]|0)+(e<<2)>>2];if((c[t>>2]|0)<(c[w>>2]<<1|0)){Q=45;break}c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[w>>2]|0)){break}c[(c[n>>2]|0)+((c[u>>2]<<1)+1<<2)>>2]=-1;c[(c[n>>2]|0)+(c[u>>2]<<1<<2)>>2]=-1;c[u>>2]=(c[u>>2]|0)+1}c[A>>2]=0;c[z>>2]=0;e=c[v>>2]|0;d=c[A>>2]|0;c[A>>2]=d+1;c[(c[m>>2]|0)+(d<<2)>>2]=e;c[(c[n>>2]|0)+((c[v>>2]<<1)+1<<2)>>2]=-2;c[(c[n>>2]|0)+(c[v>>2]<<1<<2)>>2]=-2;while(1){if((c[z>>2]|0)>=(c[A>>2]|0)){break}c[v>>2]=c[(c[m>>2]|0)+(c[z>>2]<<2)>>2];c[J>>2]=c[(c[n>>2]|0)+((c[v>>2]<<1)+1<<2)>>2];if((c[J>>2]|0)>=0){if((c[(c[o>>2]|0)+(c[J>>2]<<2)>>2]|0)!=(c[v>>2]|0)){Q=53;break a}c[(c[o>>2]|0)+(c[J>>2]<<2)>>2]=-3}c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[t>>2]|0)){break}if(!((c[(c[o>>2]|0)+(c[(c[l>>2]|0)+(c[u>>2]<<2)>>2]<<2)>>2]|0)!=-1)){if((c[(c[p>>2]|0)+(c[v>>2]<<2)>>2]|0)==1?(c[J>>2]|0)>=0:0){break}c[K>>2]=0;while(1){if((c[K>>2]|0)>=4){break}if((c[(c[q>>2]|0)+((c[(c[l>>2]|0)+(c[u>>2]<<2)>>2]<<2)+(c[K>>2]|0)<<2)>>2]|0)==(c[v>>2]|0)?(hc(c[g>>2]|0,c[h>>2]|0,(c[(c[l>>2]|0)+(c[u>>2]<<2)>>2]|0)%(c[g>>2]|0)|0,(c[(c[l>>2]|0)+(c[u>>2]<<2)>>2]|0)/(c[g>>2]|0)|0,c[o>>2]|0,c[v>>2]|0)|0)!=0:0){break}c[K>>2]=(c[K>>2]|0)+1}if((c[K>>2]|0)!=4){break}}c[u>>2]=(c[u>>2]|0)+1}if((c[u>>2]|0)<(c[t>>2]|0)){Q=68;break}c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[t>>2]|0)){break}c[M>>2]=c[(c[o>>2]|0)+(c[(c[l>>2]|0)+(c[u>>2]<<2)>>2]<<2)>>2];b:do{if(((c[M>>2]|0)>=0?!((c[(c[n>>2]|0)+(c[M>>2]<<1<<2)>>2]|0)!=-1):0)?(c[(c[r>>2]|0)+(c[(c[l>>2]|0)+(c[u>>2]<<2)>>2]<<2)>>2]|0)!=0:0){c[L>>2]=0;while(1){if((c[L>>2]|0)>=4){break b}if((c[(c[q>>2]|0)+((c[(c[l>>2]|0)+(c[u>>2]<<2)>>2]<<2)+(c[L>>2]|0)<<2)>>2]|0)==(c[v>>2]|0)?(hc(c[g>>2]|0,c[h>>2]|0,(c[(c[l>>2]|0)+(c[u>>2]<<2)>>2]|0)%(c[g>>2]|0)|0,(c[(c[l>>2]|0)+(c[u>>2]<<2)>>2]|0)/(c[g>>2]|0)|0,c[o>>2]|0,c[v>>2]|0)|0)!=0:0){break}c[L>>2]=(c[L>>2]|0)+1}if((c[A>>2]|0)>=(c[w>>2]|0)){Q=83;break a}e=c[M>>2]|0;d=c[A>>2]|0;c[A>>2]=d+1;c[(c[m>>2]|0)+(d<<2)>>2]=e;c[(c[n>>2]|0)+(c[M>>2]<<1<<2)>>2]=c[v>>2];c[(c[n>>2]|0)+((c[M>>2]<<1)+1<<2)>>2]=c[(c[l>>2]|0)+(c[u>>2]<<2)>>2]}}while(0);c[u>>2]=(c[u>>2]|0)+1}if((c[J>>2]|0)>=0){c[(c[o>>2]|0)+(c[J>>2]<<2)>>2]=c[v>>2]}c[z>>2]=(c[z>>2]|0)+1}if((Q|0)==68){Q=0;c[u>>2]=c[(c[l>>2]|0)+(c[u>>2]<<2)>>2];if((c[J>>2]|0)>=0){c[(c[o>>2]|0)+(c[J>>2]<<2)>>2]=c[v>>2]}while(1){c[(c[o>>2]|0)+(c[u>>2]<<2)>>2]=c[v>>2];R=c[v>>2]|0;if((c[(c[n>>2]|0)+(c[v>>2]<<1<<2)>>2]|0)==-2){break}c[u>>2]=c[(c[n>>2]|0)+((R<<1)+1<<2)>>2];c[v>>2]=c[(c[n>>2]|0)+(c[v>>2]<<1<<2)>>2]}e=(c[p>>2]|0)+(R<<2)|0;c[e>>2]=(c[e>>2]|0)+1}if((c[z>>2]|0)==(c[A>>2]|0)){Q=91;break}}if((Q|0)==45){Ba(48,24,403,32)}else if((Q|0)==53){Ba(64,24,424,32)}else if((Q|0)==83){Ba(80,24,550,32)}else if((Q|0)==91){c[s>>2]=0;S=c[l>>2]|0;td(S);T=c[n>>2]|0;td(T);U=c[o>>2]|0;td(U);V=c[p>>2]|0;td(V);W=c[m>>2]|0;td(W);X=c[q>>2]|0;td(X);Y=c[r>>2]|0;td(Y);_=c[s>>2]|0;i=f;return _|0}else if((Q|0)==92){c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[t>>2]|0)){Q=98;break}if((c[(c[o>>2]|0)+(c[u>>2]<<2)>>2]|0)<0){Q=96;break}if((c[(c[o>>2]|0)+(c[u>>2]<<2)>>2]|0)>=(c[w>>2]|0)){Q=96;break}c[(c[n>>2]|0)+(c[(c[o>>2]|0)+(c[u>>2]<<2)>>2]<<2)>>2]=c[u>>2];c[u>>2]=(c[u>>2]|0)+1}if((Q|0)==96){Ba(96,24,608,32)}else if((Q|0)==98){c[s>>2]=zc(c[t>>2]|0)|0;c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[t>>2]|0)){break}Cc(c[s>>2]|0,c[u>>2]|0,c[(c[n>>2]|0)+(c[(c[o>>2]|0)+(c[u>>2]<<2)>>2]<<2)>>2]|0);c[u>>2]=(c[u>>2]|0)+1}yc(c[n>>2]|0,c[t>>2]|0);c[y>>2]=0;while(1){w=(c[y>>2]|0)<(c[h>>2]|0);c[x>>2]=0;if(!w){break}while(1){$=c[y>>2]|0;if(((c[x>>2]|0)+1|0)>=(c[g>>2]|0)){break}w=Z($,c[g>>2]|0)|0;A=Z(c[y>>2]|0,c[g>>2]|0)|0;if((c[(c[o>>2]|0)+(w+(c[x>>2]|0)<<2)>>2]|0)==(c[(c[o>>2]|0)+(A+((c[x>>2]|0)+1)<<2)>>2]|0)){A=Z(c[y>>2]|0,c[g>>2]|0)|0;w=Z(c[y>>2]|0,c[g>>2]|0)|0;Cc(c[n>>2]|0,A+(c[x>>2]|0)|0,w+((c[x>>2]|0)+1)|0)}c[x>>2]=(c[x>>2]|0)+1}c[y>>2]=$+1}while(1){if((c[x>>2]|0)>=(c[g>>2]|0)){break}c[y>>2]=0;while(1){if(((c[y>>2]|0)+1|0)>=(c[h>>2]|0)){break}$=Z(c[y>>2]|0,c[g>>2]|0)|0;w=Z((c[y>>2]|0)+1|0,c[g>>2]|0)|0;if((c[(c[o>>2]|0)+($+(c[x>>2]|0)<<2)>>2]|0)==(c[(c[o>>2]|0)+(w+(c[x>>2]|0)<<2)>>2]|0)){w=Z(c[y>>2]|0,c[g>>2]|0)|0;$=Z((c[y>>2]|0)+1|0,c[g>>2]|0)|0;Cc(c[n>>2]|0,w+(c[x>>2]|0)|0,$+(c[x>>2]|0)|0)}c[y>>2]=(c[y>>2]|0)+1}c[x>>2]=(c[x>>2]|0)+1}c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[t>>2]|0)){Q=120;break}c[v>>2]=Ac(c[s>>2]|0,c[u>>2]|0)|0;x=Ac(c[n>>2]|0,c[v>>2]|0)|0;if((x|0)!=(Ac(c[n>>2]|0,c[u>>2]|0)|0)){Q=118;break}c[u>>2]=(c[u>>2]|0)+1}if((Q|0)==118){Ba(128,24,632,32)}else if((Q|0)==120){S=c[l>>2]|0;td(S);T=c[n>>2]|0;td(T);U=c[o>>2]|0;td(U);V=c[p>>2]|0;td(V);W=c[m>>2]|0;td(W);X=c[q>>2]|0;td(X);Y=c[r>>2]|0;td(Y);_=c[s>>2]|0;i=f;return _|0}}}return 0}function hc(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0;h=i;i=i+112|0;j=h+96|0;k=h+92|0;l=h+88|0;m=h+84|0;n=h+80|0;o=h+76|0;p=h+72|0;q=h+40|0;r=h+32|0;s=h+28|0;t=h+24|0;u=h+20|0;v=h+16|0;w=h+12|0;x=h+8|0;y=h+4|0;z=h;c[k>>2]=a;c[l>>2]=b;c[m>>2]=d;c[n>>2]=e;c[o>>2]=f;c[p>>2]=g;c[r>>2]=0;while(1){if((c[r>>2]|0)>=8){break}if((c[r>>2]&3|0)==2){A=0}else{if((c[r>>2]|0)>2){B=(c[r>>2]|0)<6}else{B=0}A=B?1:-1}c[t>>2]=A;if((c[r>>2]&3|0)==0){C=0}else{C=(c[r>>2]|0)<4?-1:1}c[u>>2]=C;c[v>>2]=(c[m>>2]|0)+(c[t>>2]|0);c[w>>2]=(c[n>>2]|0)+(c[u>>2]|0);if((((c[v>>2]|0)>=0?(c[v>>2]|0)<(c[k>>2]|0):0)?(c[w>>2]|0)>=0:0)?(c[w>>2]|0)<(c[l>>2]|0):0){g=Z(c[w>>2]|0,c[k>>2]|0)|0;c[q+(c[r>>2]<<2)>>2]=c[(c[o>>2]|0)+(g+(c[v>>2]|0)<<2)>>2]}else{c[q+(c[r>>2]<<2)>>2]=-1}c[r>>2]=(c[r>>2]|0)+1}if((((c[q>>2]|0)!=(c[p>>2]|0)?(c[q+8>>2]|0)!=(c[p>>2]|0):0)?(c[q+16>>2]|0)!=(c[p>>2]|0):0)?(c[q+24>>2]|0)!=(c[p>>2]|0):0){c[j>>2]=0;D=c[j>>2]|0;i=h;return D|0}c[s>>2]=0;c[r>>2]=0;while(1){if((c[r>>2]|0)>=8){break}c[x>>2]=(c[r>>2]|0)+1&7;c[y>>2]=(c[q+(c[r>>2]<<2)>>2]|0)==(c[p>>2]|0);c[z>>2]=(c[q+(c[x>>2]<<2)>>2]|0)==(c[p>>2]|0);if((c[y>>2]|0)!=(c[z>>2]|0)){c[s>>2]=(c[s>>2]|0)+1}c[r>>2]=(c[r>>2]|0)+1}c[j>>2]=(c[s>>2]|0)==2;D=c[j>>2]|0;i=h;return D|0}function ic(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,h=0,j=0,k=0;e=i;i=i+16|0;f=e+12|0;h=e+8|0;j=e+4|0;k=e;c[f>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=sd(32)|0;c[c[k>>2]>>2]=c[f>>2];c[(c[k>>2]|0)+4>>2]=c[j>>2];c[(c[k>>2]|0)+8>>2]=0;c[(c[k>>2]|0)+16>>2]=0;c[(c[k>>2]|0)+12>>2]=0;g[(c[k>>2]|0)+20>>2]=1.0;c[(c[k>>2]|0)+24>>2]=c[h>>2];c[(c[k>>2]|0)+28>>2]=0;i=e;return c[k>>2]|0}function jc(a,b,d,e,f,g,h,j){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;k=i;i=i+32|0;l=k+28|0;m=k+24|0;n=k+20|0;o=k+16|0;p=k+12|0;q=k+8|0;r=k+4|0;s=k;c[l>>2]=a;c[m>>2]=b;c[n>>2]=d;c[o>>2]=e;c[p>>2]=f;c[q>>2]=g;c[r>>2]=h;c[s>>2]=j;Mb[c[c[c[l>>2]>>2]>>2]&1](c[(c[l>>2]|0)+4>>2]|0,c[m>>2]|0,c[n>>2]|0,c[o>>2]|0,c[p>>2]|0,c[q>>2]|0,c[r>>2]|0,c[s>>2]|0);i=k;return}function kc(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0;h=i;i=i+32|0;j=h+20|0;k=h+16|0;l=h+12|0;m=h+8|0;n=h+4|0;o=h;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=f;c[o>>2]=g;Nb[c[(c[c[j>>2]>>2]|0)+4>>2]&3](c[(c[j>>2]|0)+4>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0,c[n>>2]|0,c[o>>2]|0);i=h;return}function lc(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0;h=i;i=i+32|0;j=h+20|0;k=h+16|0;l=h+12|0;m=h+8|0;n=h+4|0;o=h;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=f;c[o>>2]=g;Nb[c[(c[c[j>>2]>>2]|0)+8>>2]&3](c[(c[j>>2]|0)+4>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0,c[n>>2]|0,c[o>>2]|0);i=h;return}function mc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0;g=i;i=i+32|0;h=g+16|0;j=g+12|0;k=g+8|0;l=g+4|0;m=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;Cb[c[(c[c[h>>2]>>2]|0)+12>>2]&3](c[(c[h>>2]|0)+4>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0);i=g;return}function nc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0;g=i;i=i+32|0;h=g+16|0;j=g+12|0;k=g+8|0;l=g+4|0;m=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;if((c[(c[c[h>>2]>>2]|0)+20>>2]|0)==0){i=g;return}Cb[c[(c[c[h>>2]>>2]|0)+20>>2]&3](c[(c[h>>2]|0)+4>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0);i=g;return}function oc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0;g=i;i=i+32|0;h=g+16|0;j=g+12|0;k=g+8|0;l=g+4|0;m=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;Cb[c[(c[c[h>>2]>>2]|0)+24>>2]&3](c[(c[h>>2]|0)+4>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0);i=g;return}function pc(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;Eb[c[(c[c[d>>2]>>2]|0)+28>>2]&7](c[(c[d>>2]|0)+4>>2]|0);i=b;return}function qc(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;Eb[c[(c[c[d>>2]>>2]|0)+32>>2]&7](c[(c[d>>2]|0)+4>>2]|0);i=b;return}function rc(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;Eb[c[(c[c[d>>2]>>2]|0)+36>>2]&7](c[(c[d>>2]|0)+4>>2]|0);i=b;return}function sc(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;g=d;c[e>>2]=a;c[f>>2]=b;if((c[(c[c[e>>2]>>2]|0)+40>>2]|0)==0){i=d;return}if((c[(c[e>>2]|0)+24>>2]|0)==0){Ba(192,176,198,200)}c[g>>2]=ae(c[(c[e>>2]|0)+24>>2]|0,c[f>>2]|0)|0;if((c[(c[e>>2]|0)+28>>2]|0)!=0?($f(c[g>>2]|0,c[(c[e>>2]|0)+28>>2]|0)|0)==0:0){td(c[g>>2]|0);i=d;return}Fb[c[(c[c[e>>2]>>2]|0)+40>>2]&7](c[(c[e>>2]|0)+4>>2]|0,c[g>>2]|0);td(c[(c[e>>2]|0)+28>>2]|0);c[(c[e>>2]|0)+28>>2]=c[g>>2];i=d;return}function tc(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;b=uc(c[e>>2]|0,+(c[f>>2]|0),+(c[f>>2]|0),+(c[f>>2]|0),+(c[f>>2]|0),-1,0)|0;i=d;return b|0}function uc(a,b,d,e,f,h,j){a=a|0;b=+b;d=+d;e=+e;f=+f;h=h|0;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;k=i;i=i+32|0;l=k+24|0;m=k+20|0;n=k+16|0;o=k+12|0;p=k+8|0;q=k+4|0;r=k;c[l>>2]=a;g[m>>2]=b;g[n>>2]=d;g[o>>2]=e;g[p>>2]=f;c[q>>2]=h;c[r>>2]=j;if((c[(c[l>>2]|0)+12>>2]|0)>=(c[(c[l>>2]|0)+16>>2]|0)){c[(c[l>>2]|0)+16>>2]=(c[(c[l>>2]|0)+12>>2]|0)+16;j=ud(c[(c[l>>2]|0)+8>>2]|0,(c[(c[l>>2]|0)+16>>2]|0)*24|0)|0;c[(c[l>>2]|0)+8>>2]=j}c[(c[(c[l>>2]|0)+8>>2]|0)+((c[(c[l>>2]|0)+12>>2]|0)*24|0)>>2]=c[q>>2];c[(c[(c[l>>2]|0)+8>>2]|0)+((c[(c[l>>2]|0)+12>>2]|0)*24|0)+4>>2]=c[r>>2];g[(c[(c[l>>2]|0)+8>>2]|0)+((c[(c[l>>2]|0)+12>>2]|0)*24|0)+8>>2]=+g[m>>2];g[(c[(c[l>>2]|0)+8>>2]|0)+((c[(c[l>>2]|0)+12>>2]|0)*24|0)+12>>2]=+g[n>>2];g[(c[(c[l>>2]|0)+8>>2]|0)+((c[(c[l>>2]|0)+12>>2]|0)*24|0)+16>>2]=+g[o>>2];g[(c[(c[l>>2]|0)+8>>2]|0)+((c[(c[l>>2]|0)+12>>2]|0)*24|0)+20>>2]=+g[p>>2];p=(c[l>>2]|0)+12|0;l=c[p>>2]|0;c[p>>2]=l+1;i=k;return l|0}function vc(a,b){a=a|0;b=+b;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;g[f>>2]=b;a=uc(c[e>>2]|0,+g[f>>2],+g[f>>2],+g[f>>2],+g[f>>2],-1,0)|0;i=d;return a|0}function wc(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,h=0.0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;h=+N(+(+g[(c[e>>2]|0)+20>>2]));Bb[c[(c[c[e>>2]>>2]|0)+84>>2]&0](c[(c[e>>2]|0)+4>>2]|0,h*+(c[f>>2]|0));i=d;return}function xc(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;Fb[c[(c[c[e>>2]>>2]|0)+88>>2]&7](c[(c[e>>2]|0)+4>>2]|0,c[f>>2]|0);i=d;return}function yc(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;g=d;c[e>>2]=a;c[f>>2]=b;c[g>>2]=0;while(1){if((c[g>>2]|0)>=(c[f>>2]|0)){break}c[(c[e>>2]|0)+(c[g>>2]<<2)>>2]=6;c[g>>2]=(c[g>>2]|0)+1}i=d;return}function zc(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;c[e>>2]=sd(c[d>>2]<<2)|0;yc(c[e>>2]|0,c[d>>2]|0);i=b;return c[e>>2]|0}function Ac(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;b=Bc(c[e>>2]|0,c[f>>2]|0,0)|0;i=d;return b|0}function Bc(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;e=i;i=i+32|0;f=e+28|0;g=e+24|0;h=e+20|0;j=e+16|0;k=e+12|0;l=e+8|0;m=e+4|0;n=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;c[j>>2]=c[g>>2];c[l>>2]=0;if((c[g>>2]|0)<0){Ba(216,232,110,240)}while(1){o=c[g>>2]|0;if((c[(c[f>>2]|0)+(c[g>>2]<<2)>>2]&2|0)!=0){break}c[l>>2]=c[l>>2]^c[(c[f>>2]|0)+(o<<2)>>2]&1;c[g>>2]=c[(c[f>>2]|0)+(c[g>>2]<<2)>>2]>>2}c[k>>2]=o;if((c[h>>2]|0)!=0){c[c[h>>2]>>2]=c[l>>2]}c[g>>2]=c[j>>2];while(1){if((c[g>>2]|0)==(c[k>>2]|0)){break}c[m>>2]=c[(c[f>>2]|0)+(c[g>>2]<<2)>>2]>>2;c[n>>2]=c[l>>2]^c[(c[f>>2]|0)+(c[g>>2]<<2)>>2]&1;c[(c[f>>2]|0)+(c[g>>2]<<2)>>2]=c[k>>2]<<2|c[l>>2];c[l>>2]=c[n>>2];c[g>>2]=c[m>>2]}if((c[l>>2]|0)==0){i=e;return c[g>>2]|0}else{Ba(256,232,137,240)}return 0}function Cc(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0;e=i;i=i+16|0;f=e+8|0;g=e+4|0;h=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;Dc(c[f>>2]|0,c[g>>2]|0,c[h>>2]|0,0);i=e;return}function Dc(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;f=i;i=i+32|0;g=f+24|0;h=f+20|0;j=f+16|0;k=f+12|0;l=f+8|0;m=f+4|0;n=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[h>>2]=Bc(c[g>>2]|0,c[h>>2]|0,l)|0;if((c[(c[g>>2]|0)+(c[h>>2]<<2)>>2]&2|0)==0){Ba(272,232,152,288)}c[k>>2]=c[k>>2]^c[l>>2];c[j>>2]=Bc(c[g>>2]|0,c[j>>2]|0,m)|0;if((c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]&2|0)==0){Ba(304,232,155,288)}c[k>>2]=c[k>>2]^c[m>>2];l=c[k>>2]|0;do{if((c[h>>2]|0)==(c[j>>2]|0)){if((l|0)!=0){Ba(320,232,161,288)}else{break}}else{if(!((l|0)==0|(c[k>>2]|0)==1)){Ba(336,232,163,288)}if((c[h>>2]|0)>(c[j>>2]|0)){c[n>>2]=c[h>>2];c[h>>2]=c[j>>2];c[j>>2]=c[n>>2]}e=(c[g>>2]|0)+(c[h>>2]<<2)|0;c[e>>2]=(c[e>>2]|0)+(c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]>>2<<2);c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]=c[h>>2]<<2|((c[k>>2]|0)!=0^1^1)&1}}while(0);c[j>>2]=Bc(c[g>>2]|0,c[j>>2]|0,m)|0;if((c[j>>2]|0)!=(c[h>>2]|0)){Ba(368,232,188,288)}if((c[m>>2]|0)==(c[k>>2]|0)){i=f;return}else{Ba(384,232,189,288)}}function Ec(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;g=d;c[e>>2]=a;c[f>>2]=b;c[g>>2]=sd(8)|0;eb(c[g>>2]|0);c[c[e>>2]>>2]=c[g>>2];c[c[f>>2]>>2]=8;i=d;return}function Fc(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0;d=i;i=i+544|0;e=d+16|0;f=d+24|0;g=d;c[e>>2]=a;gg(f|0,400)|0;c[g>>2]=b;b=f+(bg(f|0)|0)|0;a=512-(bg(f|0)|0)|0;ib(b|0,a|0,c[e>>2]|0,g|0)|0;ua(f|0);i=d;return}function Gc(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;g=d;c[f>>2]=a;c[g>>2]=b;if((c[f>>2]|0)!=0?(c[g>>2]|0)!=0:0){c[e>>2]=$f(c[f>>2]|0,c[g>>2]|0)|0;h=c[e>>2]|0;i=d;return h|0}if((c[f>>2]|0)!=0){j=1}else{j=(c[g>>2]|0)!=0?-1:0}c[e>>2]=j;h=c[e>>2]|0;i=d;return h|0}function Hc(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;hb();c[106]=0;i=b;return}function Ic(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;if((c[106]|0)!=0){i=b;return}kb();c[106]=1;i=b;return}function Jc(a){a=+a;var b=0,d=0;b=i;i=i+16|0;d=b;h[d>>3]=a;if((c[106]|0)==0){i=b;return}Od(c[108]|0,+h[d>>3]);i=b;return}function Kc(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;zd(c[108]|0,e,f,1);if((c[110]|0)==(c[e>>2]|0)?(c[112]|0)==(c[f>>2]|0):0){i=d;return}Ea(c[e>>2]|0,c[f>>2]|0);c[110]=c[e>>2];c[112]=c[f>>2];Cd(c[108]|0);i=d;return}function Lc(a,b){a=a|0;b=b|0;var d=0;d=i;i=i+16|0;c[d+4>>2]=a;c[d>>2]=b;wd(c[108]|0);Mc();Cd(c[108]|0);i=d;return}function Mc(){var a=0,b=0,d=0;a=i;i=i+16|0;b=a+4|0;d=a;c[d>>2]=2147483647;c[b>>2]=2147483647;zd(c[108]|0,b,d,0);Ea(c[b>>2]|0,c[d>>2]|0);c[110]=c[b>>2];c[112]=c[d>>2];i=a;return}function Nc(a,b){a=a|0;b=b|0;var d=0,e=0;d=i;i=i+16|0;e=d;c[d+4>>2]=a;c[e>>2]=b;g[(c[e>>2]|0)+8>>2]=.8999999761581421;g[(c[e>>2]|0)+4>>2]=.8999999761581421;g[c[e>>2]>>2]=.8999999761581421;i=d;return}function Oc(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0;e=i;i=i+16|0;f=e+8|0;g=e+4|0;h=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;if((c[h>>2]|0)==0){j=512}else{j=(c[h>>2]|0)==1?513:514}c[h>>2]=j;Md(c[108]|0,c[f>>2]|0,c[g>>2]|0,c[h>>2]|0)|0;Pc();i=e;return}function Pc(){var a=0,b=0;a=i;b=Hd(c[108]|0)|0;Qa(b|0,Id(c[108]|0)|0);i=a;return}function Qc(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0;e=i;i=i+16|0;f=e+8|0;g=e+4|0;h=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;if((c[h>>2]|0)==0){j=518}else{j=(c[h>>2]|0)==1?519:520}c[h>>2]=j;Md(c[108]|0,c[f>>2]|0,c[g>>2]|0,c[h>>2]|0)|0;Pc();i=e;return}function Rc(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0;e=i;i=i+16|0;f=e+12|0;g=e+8|0;h=e+4|0;j=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;if((c[h>>2]&2|0)!=0){k=516}else{k=(c[h>>2]&4|0)!=0?517:515}c[j>>2]=k;Md(c[108]|0,c[f>>2]|0,c[g>>2]|0,c[j>>2]|0)|0;Pc();i=e;return}function Sc(b,d,e,f,g,h){b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;var j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0;j=i;i=i+32|0;k=j+24|0;l=j+16|0;m=j+12|0;n=j+8|0;o=j+4|0;p=j;c[k>>2]=b;c[j+20>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=g;c[o>>2]=h;c[p>>2]=-1;do{if(((Gc(c[l>>2]|0,456)|0)!=0?(Gc(c[l>>2]|0,472)|0)!=0:0)?!((c[k>>2]|0)==8|(c[k>>2]|0)==46):0){if((Gc(c[l>>2]|0,480)|0)!=0?(c[k>>2]|0)!=13:0){if((Gc(c[l>>2]|0,488)|0)!=0?(c[k>>2]|0)!=37:0){if((Gc(c[l>>2]|0,496)|0)!=0?(c[k>>2]|0)!=38:0){if((Gc(c[l>>2]|0,504)|0)!=0?(c[k>>2]|0)!=39:0){if((Gc(c[l>>2]|0,512)|0)!=0?(c[k>>2]|0)!=40:0){if((Gc(c[l>>2]|0,520)|0)!=0?(c[k>>2]|0)!=35:0){if((Gc(c[l>>2]|0,528)|0)!=0?(c[k>>2]|0)!=34:0){if((Gc(c[l>>2]|0,544)|0)!=0?(c[k>>2]|0)!=36:0){if((Gc(c[l>>2]|0,552)|0)!=0?(c[k>>2]|0)!=33:0){if(((c[m>>2]|0)!=0?(a[c[m>>2]|0]|0)!=0:0)?(a[(c[m>>2]|0)+1|0]|0)==0:0){c[p>>2]=a[c[m>>2]|0]&255;break}h=c[k>>2]|0;if((c[k>>2]|0)>=96&(c[k>>2]|0)<106){c[p>>2]=16384|48+h-96;break}g=c[k>>2]|0;if((h|0)>=65&(c[k>>2]|0)<=90){c[p>>2]=g+((c[n>>2]|0)!=0?0:32);break}h=c[k>>2]|0;if((g|0)>=48&(c[k>>2]|0)<=57){c[p>>2]=h;break}if((h|0)!=32){break}c[p>>2]=c[k>>2];break}c[p>>2]=16441;break}c[p>>2]=16439;break}c[p>>2]=16435;break}c[p>>2]=16433;break}c[p>>2]=522;break}c[p>>2]=524;break}c[p>>2]=521;break}c[p>>2]=523;break}c[p>>2]=13}else{q=4}}while(0);if((q|0)==4){c[p>>2]=127}if((c[p>>2]|0)<0){i=j;return}if((c[n>>2]|0)!=0?(c[p>>2]|0)>=256:0){c[p>>2]=c[p>>2]|8192}do{if((c[o>>2]|0)!=0){n=c[p>>2]|0;if((c[p>>2]|0)>=256){c[p>>2]=n|4096;break}else{c[p>>2]=n&31;break}}}while(0);Md(c[108]|0,0,0,c[p>>2]|0)|0;Pc();i=j;return}function Tc(a,b,d,e,f,g,h,j){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0;k=i;i=i+128|0;l=k;m=k+36|0;n=k+32|0;o=k+28|0;p=k+24|0;q=k+20|0;r=k+16|0;s=k+12|0;t=k+48|0;u=k+8|0;c[k+40>>2]=a;c[m>>2]=b;c[n>>2]=d;c[o>>2]=e;c[p>>2]=f;c[q>>2]=g;c[r>>2]=h;c[s>>2]=j;j=(c[o>>2]|0)==0?776:792;c[l>>2]=c[p>>2];c[l+4>>2]=j;ab(t|0,768,l|0)|0;if((c[q>>2]&256|0)!=0){l=Aa(c[p>>2]|0,t|0)|0;c[n>>2]=(c[n>>2]|0)+l}do{if((c[q>>2]&1|0)==0){if((c[q>>2]&2|0)!=0){c[u>>2]=2;break}else{c[u>>2]=0;break}}else{c[u>>2]=1}}while(0);Ua(c[m>>2]|0,c[n>>2]|0,c[u>>2]|0,c[(c[184]|0)+(c[r>>2]<<2)>>2]|0,t|0,c[s>>2]|0);i=k;return}function Uc(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0;h=i;i=i+32|0;j=h+16|0;k=h+12|0;l=h+8|0;m=h+4|0;n=h;c[h+20>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=g;Ha(c[j>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0,c[(c[184]|0)+(c[n>>2]<<2)>>2]|0);i=h;return}function Vc(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0;h=i;i=i+32|0;j=h+16|0;k=h+12|0;l=h+8|0;m=h+4|0;n=h;c[h+20>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=g;ya(+(+(c[j>>2]|0)),+(+(c[k>>2]|0)),+(+(c[l>>2]|0)),+(+(c[m>>2]|0)),1,c[(c[184]|0)+(c[n>>2]<<2)>>2]|0);i=h;return}function Wc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0;g=i;i=i+32|0;h=g+12|0;j=g+8|0;k=g+4|0;l=g;c[g+16>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=f;if((c[k>>2]|0)>=0){m=c[(c[184]|0)+(c[k>>2]<<2)>>2]|0}else{m=0}Ta(c[h>>2]|0,c[j>>2]|0,m|0,c[(c[184]|0)+(c[l>>2]<<2)>>2]|0);i=g;return}function Xc(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0;h=i;i=i+32|0;j=h+16|0;k=h+12|0;l=h+8|0;m=h+4|0;n=h;c[h+20>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=g;if((c[m>>2]|0)>=0){o=c[(c[184]|0)+(c[m>>2]<<2)>>2]|0}else{o=0}Ga(c[j>>2]|0,c[k>>2]|0,c[l>>2]|0,o|0,c[(c[184]|0)+(c[n>>2]<<2)>>2]|0);i=h;return}function Yc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0;g=i;i=i+32|0;h=g+12|0;j=g+8|0;k=g+4|0;l=g;c[g+16>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=f;rd(h,j,k,l);if((c[k>>2]|0)<=0){i=g;return}if((c[l>>2]|0)<=0){i=g;return}Wa(c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0);i=g;return}function Zc(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0;g=i;i=i+32|0;h=g+12|0;j=g+8|0;k=g+4|0;l=g;c[g+16>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=f;vb(c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0);i=g;return}function _c(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;Sa();i=b;return}function $c(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;bb();i=b;return}function ad(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;lb();i=b;return}function bd(a,b){a=a|0;b=b|0;var d=0,e=0;d=i;i=i+16|0;e=d;c[d+4>>2]=a;c[e>>2]=b;sb(c[e>>2]|0);i=d;return}function cd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0;e=i;i=i+16|0;f=e+8|0;g=e+4|0;h=e;c[e+12>>2]=a;c[f>>2]=b;c[g>>2]=d;c[h>>2]=sd(12)|0;c[(c[h>>2]|0)+4>>2]=c[f>>2];c[(c[h>>2]|0)+8>>2]=c[g>>2];d=La(c[f>>2]|0,c[g>>2]|0)|0;c[c[h>>2]>>2]=d;i=e;return c[h>>2]|0}function dd(a,b){a=a|0;b=b|0;var d=0,e=0;d=i;i=i+16|0;e=d;c[d+4>>2]=a;c[e>>2]=b;mb(c[c[e>>2]>>2]|0);td(c[e>>2]|0);i=d;return}function ed(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0;f=i;i=i+32|0;g=f+16|0;h=f+12|0;j=f+8|0;k=f+4|0;l=f;c[f+20>>2]=a;c[g>>2]=b;c[h>>2]=d;c[j>>2]=e;c[k>>2]=c[(c[g>>2]|0)+4>>2];c[l>>2]=c[(c[g>>2]|0)+8>>2];rd(h,j,k,l);if((c[k>>2]|0)<=0){i=f;return}if((c[l>>2]|0)<=0){i=f;return}pb(c[c[g>>2]>>2]|0,c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0);i=f;return}function fd(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0;f=i;i=i+32|0;g=f+16|0;h=f+12|0;j=f+8|0;k=f+4|0;l=f;c[f+20>>2]=a;c[g>>2]=b;c[h>>2]=d;c[j>>2]=e;c[k>>2]=c[(c[g>>2]|0)+4>>2];c[l>>2]=c[(c[g>>2]|0)+8>>2];rd(h,j,k,l);if((c[k>>2]|0)<=0){i=f;return}if((c[l>>2]|0)<=0){i=f;return}jb(c[c[g>>2]>>2]|0,c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0);i=f;return}function gd(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0;e=i;i=i+16|0;f=e+4|0;c[e+8>>2]=a;c[f>>2]=b;c[e>>2]=d;d=vd(c[c[f>>2]>>2]|0)|0;i=e;return d|0}function hd(a,b,d,e,f,h,j){a=a|0;b=+b;d=+d;e=+e;f=+f;h=+h;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0;k=i;i=i+32|0;l=k+20|0;m=k+16|0;n=k+12|0;o=k+8|0;p=k+4|0;q=k;c[k+24>>2]=a;g[l>>2]=b;g[m>>2]=d;g[n>>2]=e;g[o>>2]=f;g[p>>2]=h;c[q>>2]=j;ya(+(+g[m>>2]),+(+g[n>>2]),+(+g[o>>2]),+(+g[p>>2]),~~+g[l>>2]|0,c[(c[184]|0)+(c[q>>2]<<2)>>2]|0);i=k;return}function id(){var a=0,b=0;a=i;i=i+16|0;b=a;if((c[166]|0)==0){i=a;return}c[b>>2]=Sd(c[108]|0)|0;wa(((c[b>>2]|0)<0?-1:c[b>>2]|0)|0);i=a;return}function jd(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;td(c[(c[168]|0)+(c[e>>2]<<4)+8>>2]|0);b=vd(c[f>>2]|0)|0;c[(c[168]|0)+(c[e>>2]<<4)+8>>2]=b;i=d;return}function kd(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;c[(c[168]|0)+(c[e>>2]<<4)+12>>2]=c[f>>2];i=d;return}function ld(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+8|0;e=b+4|0;f=b;c[d>>2]=a;switch(c[d>>2]|0){case 7:{Md(c[108]|0,0,0,117)|0;Pc();Da();i=b;return};case 8:{Md(c[108]|0,0,0,114)|0;Pc();Da();i=b;return};case 9:{if((c[1744>>2]|0)!=0?(c[f>>2]=$d(c[108]|0)|0,(c[f>>2]|0)!=0):0){ua(c[f>>2]|0)}Pc();Da();i=b;return};case 2:{c[e>>2]=yb()|0;if((c[e>>2]|0)<0){if((c[1708>>2]|0)==0){i=b;return}md(0);i=b;return}else{if((c[e>>2]|0)>=(c[170]|0)){Ba(688,704,692,712)}Bd(c[108]|0,c[(c[180]|0)+(c[e>>2]<<2)>>2]|0);Ed(c[108]|0);Mc();Dd(c[108]|0);Pc();Da();id();i=b;return}break};case 3:{nd(1);Pc();i=b;return};case 4:{nd(0);Pc();i=b;return};case 5:{Md(c[108]|0,0,0,110)|0;Pc();Da();i=b;return};case 6:{Kd(c[108]|0);Pc();Da();i=b;return};case 1:{md(1);i=b;return};case 0:{md(2);i=b;return};default:{i=b;return}}}function md(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+8|0;e=b+4|0;f=b;c[d>>2]=a;c[168]=Vd(c[108]|0,c[d>>2]|0,e)|0;c[190]=c[d>>2];xa(c[e>>2]|0);td(c[e>>2]|0);c[f>>2]=0;while(1){if((c[(c[168]|0)+(c[f>>2]<<4)+4>>2]|0)==3){break}e=c[(c[168]|0)+(c[f>>2]<<4)+4>>2]|0;if((e|0)==2){Ka(c[f>>2]|0,c[(c[168]|0)+(c[f>>2]<<4)>>2]|0,c[(c[168]|0)+(c[f>>2]<<4)+12>>2]|0)}else if((e|0)==0){Va(c[f>>2]|0,c[(c[168]|0)+(c[f>>2]<<4)>>2]|0,c[(c[168]|0)+(c[f>>2]<<4)+8>>2]|0)}else if((e|0)==1){ob(c[f>>2]|0,c[(c[168]|0)+(c[f>>2]<<4)>>2]|0,c[(c[168]|0)+(c[f>>2]<<4)+8>>2]|0,c[(c[168]|0)+(c[f>>2]<<4)+12>>2]|0)}c[f>>2]=(c[f>>2]|0)+1}Fa();i=b;return}function nd(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;if((c[d>>2]|0)==0){id();de(c[168]|0);va();i=b;return}c[e>>2]=_d(c[108]|0,c[190]|0,c[168]|0)|0;if((c[e>>2]|0)!=0){ua(c[e>>2]|0);i=b;return}else{id();Ed(c[108]|0);Mc();Dd(c[108]|0);de(c[168]|0);va();i=b;return}}function od(b,d){b=b|0;d=d|0;var e=0,f=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;e=i;i=i+80|0;f=e;h=e+32|0;j=e+28|0;k=e+24|0;l=e+20|0;m=e+16|0;n=e+12|0;o=e+40|0;c[e+36>>2]=0;c[h>>2]=b;c[j>>2]=d;c[108]=xd(0,1672,560,0)|0;if(((c[h>>2]|0)>1?(a[c[(c[j>>2]|0)+4>>2]|0]|0)==35:0)?(a[(c[(c[j>>2]|0)+4>>2]|0)+1|0]|0)!=0:0){c[k>>2]=Wd(c[108]|0,(c[(c[j>>2]|0)+4>>2]|0)+1|0)|0}else{c[k>>2]=0}Ed(c[108]|0);Mc();if((Td(c[108]|0)|0)!=0){Pa()}c[170]=Qd(c[108]|0)|0;if((c[170]|0)==0){Za();c[166]=0}else{c[180]=sd(c[170]<<2)|0;c[m>>2]=0;while(1){if((c[m>>2]|0)>=(c[170]|0)){break}Rd(c[108]|0,c[m>>2]|0,n,(c[180]|0)+(c[m>>2]<<2)|0);tb(c[n>>2]|0);c[m>>2]=(c[m>>2]|0)+1}if((c[1708>>2]|0)!=0){tb(0)}c[166]=1;id()}if((c[1744>>2]|0)==0){_a()}c[l>>2]=Pd(c[108]|0,728)|0;c[184]=sd(c[182]<<2)|0;c[m>>2]=0;while(1){if((c[m>>2]|0)>=(c[182]|0)){break}n=~~(+g[(c[l>>2]|0)+(((c[m>>2]|0)*3|0)+1<<2)>>2]*255.0+.5)>>>0;j=~~(+g[(c[l>>2]|0)+(((c[m>>2]|0)*3|0)+2<<2)>>2]*255.0+.5)>>>0;c[f>>2]=~~(+g[(c[l>>2]|0)+(((c[m>>2]|0)*3|0)+0<<2)>>2]*255.0+.5)>>>0;c[f+4>>2]=n;c[f+8>>2]=j;ab(o|0,744,f|0)|0;j=vd(o)|0;c[(c[184]|0)+(c[m>>2]<<2)>>2]=j;c[m>>2]=(c[m>>2]|0)+1}Ud(c[108]|0,7,0);Dd(c[108]|0);qd();Pc();if((c[k>>2]|0)==0){i=e;return 0}ua(c[k>>2]|0);i=e;return 0}function pd(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;qd();i=b;return}function qd(){var a=0,b=0,d=0;a=i;i=i+16|0;b=a+4|0;d=a;c[b>>2]=Yd(c[108]|0)|0;c[d>>2]=Zd(c[108]|0)|0;Xa(c[b>>2]|0,c[d>>2]|0);td(c[b>>2]|0);td(c[d>>2]|0);i=a;return}function rd(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;f=i;i=i+32|0;g=f+28|0;h=f+24|0;j=f+20|0;k=f+16|0;l=f+12|0;m=f+8|0;n=f+4|0;o=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=c[c[g>>2]>>2];c[n>>2]=c[c[h>>2]>>2];c[m>>2]=(c[c[g>>2]>>2]|0)+(c[c[j>>2]>>2]|0);c[o>>2]=(c[c[h>>2]>>2]|0)+(c[c[k>>2]>>2]|0);if((c[l>>2]|0)<0){p=0}else{p=(c[l>>2]|0)>(c[110]|0)?c[110]|0:c[l>>2]|0}c[l>>2]=p;if((c[m>>2]|0)<0){q=0}else{q=(c[m>>2]|0)>(c[110]|0)?c[110]|0:c[m>>2]|0}c[m>>2]=q;if((c[n>>2]|0)<0){r=0}else{r=(c[n>>2]|0)>(c[112]|0)?c[112]|0:c[n>>2]|0}c[n>>2]=r;if((c[o>>2]|0)<0){s=0}else{s=(c[o>>2]|0)>(c[112]|0)?c[112]|0:c[o>>2]|0}c[o>>2]=s;c[c[g>>2]>>2]=c[l>>2];c[c[h>>2]>>2]=c[n>>2];c[c[j>>2]>>2]=(c[m>>2]|0)-(c[l>>2]|0);c[c[k>>2]>>2]=(c[o>>2]|0)-(c[n>>2]|0);i=f;return}function sd(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+8|0;e=b+4|0;c[d>>2]=a;c[e>>2]=Uf(c[d>>2]|0)|0;if((c[e>>2]|0)!=0){f=c[e>>2]|0;i=b;return f|0}Fc(808,b);f=c[e>>2]|0;i=b;return f|0}function td(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[d>>2]|0)==0){i=b;return}Vf(c[d>>2]|0);i=b;return}function ud(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0;d=i;i=i+16|0;e=d+12|0;f=d+8|0;g=d+4|0;c[e>>2]=a;c[f>>2]=b;if((c[e>>2]|0)!=0){c[g>>2]=Wf(c[e>>2]|0,c[f>>2]|0)|0}else{c[g>>2]=Uf(c[f>>2]|0)|0}if((c[g>>2]|0)!=0){h=c[g>>2]|0;i=d;return h|0}Fc(808,d);h=c[g>>2]|0;i=d;return h|0}function vd(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;c[e>>2]=sd(1+(bg(c[d>>2]|0)|0)|0)|0;gg(c[e>>2]|0,c[d>>2]|0)|0;i=b;return c[e>>2]|0}function wd(b){b=b|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;e=i;i=i+112|0;f=e;g=e+20|0;h=e+24|0;j=e+16|0;k=e+12|0;l=e+8|0;m=e+4|0;c[g>>2]=b;c[(c[g>>2]|0)+128>>2]=c[(c[(c[g>>2]|0)+8>>2]|0)+120>>2];c[f>>2]=c[c[(c[g>>2]|0)+8>>2]>>2];ab(h|0,824,f|0)|0;c[l>>2]=0;c[k>>2]=0;while(1){if((a[h+(c[k>>2]|0)|0]|0)==0){break}if((Ya(d[h+(c[k>>2]|0)|0]|0)|0)==0){b=(db(d[h+(c[k>>2]|0)|0]|0)|0)&255;n=c[l>>2]|0;c[l>>2]=n+1;a[h+n|0]=b}c[k>>2]=(c[k>>2]|0)+1}a[h+(c[l>>2]|0)|0]=0;l=$a(h|0)|0;c[j>>2]=l;if((l|0)==0){i=e;return}l=c[j>>2]|0;c[f>>2]=m;j=(Ia(l|0,840,f|0)|0)==1;if(!(j&(c[m>>2]|0)>0)){i=e;return}c[(c[g>>2]|0)+128>>2]=c[m>>2];i=e;return}function xd(b,e,f,h){b=b|0;e=e|0;f=f|0;h=h|0;var j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;j=i;i=i+128|0;k=j;l=j+40|0;m=j+36|0;n=j+32|0;o=j+28|0;p=j+24|0;q=j+20|0;r=j+16|0;s=j+48|0;t=j+12|0;u=j+8|0;v=j+4|0;c[l>>2]=b;c[m>>2]=e;c[n>>2]=f;c[o>>2]=h;c[p>>2]=sd(152)|0;Ec(q,r);c[c[p>>2]>>2]=c[l>>2];c[(c[p>>2]|0)+8>>2]=c[m>>2];l=oe(c[q>>2]|0,c[r>>2]|0)|0;c[(c[p>>2]|0)+4>>2]=l;c[(c[p>>2]|0)+60>>2]=0;c[(c[p>>2]|0)+56>>2]=0;c[(c[p>>2]|0)+52>>2]=0;c[(c[p>>2]|0)+64>>2]=0;l=Db[c[(c[m>>2]|0)+12>>2]&1]()|0;c[(c[p>>2]|0)+68>>2]=l;c[(c[p>>2]|0)+144>>2]=0;c[(c[p>>2]|0)+148>>2]=0;c[k>>2]=c[c[(c[p>>2]|0)+8>>2]>>2];ab(s|0,848,k|0)|0;c[v>>2]=0;c[u>>2]=0;while(1){if((a[s+(c[u>>2]|0)|0]|0)==0){break}if((Ya(d[s+(c[u>>2]|0)|0]|0)|0)==0){k=(db(d[s+(c[u>>2]|0)|0]|0)|0)&255;l=c[v>>2]|0;c[v>>2]=l+1;a[s+l|0]=k}c[u>>2]=(c[u>>2]|0)+1}a[s+(c[v>>2]|0)|0]=0;v=$a(s|0)|0;c[t>>2]=v;if((v|0)!=0){Fb[c[(c[(c[p>>2]|0)+8>>2]|0)+20>>2]&7](c[(c[p>>2]|0)+68>>2]|0,c[t>>2]|0)}c[(c[p>>2]|0)+72>>2]=0;c[(c[p>>2]|0)+36>>2]=0;c[(c[p>>2]|0)+32>>2]=0;c[(c[p>>2]|0)+40>>2]=0;c[(c[p>>2]|0)+44>>2]=0;c[(c[p>>2]|0)+48>>2]=2;c[(c[p>>2]|0)+76>>2]=0;c[(c[p>>2]|0)+84>>2]=0;c[(c[p>>2]|0)+12>>2]=0;c[(c[p>>2]|0)+16>>2]=0;c[(c[p>>2]|0)+20>>2]=0;c[(c[p>>2]|0)+28>>2]=0;c[(c[p>>2]|0)+24>>2]=0;g[(c[p>>2]|0)+92>>2]=0.0;g[(c[p>>2]|0)+88>>2]=0.0;g[(c[p>>2]|0)+100>>2]=0.0;g[(c[p>>2]|0)+96>>2]=0.0;c[(c[p>>2]|0)+104>>2]=0;c[(c[p>>2]|0)+80>>2]=0;c[(c[p>>2]|0)+124>>2]=0;c[(c[p>>2]|0)+116>>2]=0;c[(c[p>>2]|0)+108>>2]=0;g[(c[p>>2]|0)+112>>2]=0.0;c[(c[p>>2]|0)+140>>2]=0;c[(c[p>>2]|0)+136>>2]=0;c[(c[p>>2]|0)+132>>2]=0;if((c[n>>2]|0)!=0){t=ic(c[n>>2]|0,c[p>>2]|0,c[o>>2]|0)|0;c[(c[p>>2]|0)+120>>2]=t;w=c[p>>2]|0;wd(w);x=c[q>>2]|0;td(x);y=c[p>>2]|0;i=j;return y|0}else{c[(c[p>>2]|0)+120>>2]=0;w=c[p>>2]|0;wd(w);x=c[q>>2]|0;td(x);y=c[p>>2]|0;i=j;return y|0}return 0}function yd(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b;c[d>>2]=a;while(1){e=c[d>>2]|0;if((c[(c[d>>2]|0)+52>>2]|0)<=0){break}a=e+52|0;c[a>>2]=(c[a>>2]|0)+ -1;Eb[c[(c[(c[d>>2]|0)+8>>2]|0)+68>>2]&7](c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)>>2]|0);td(c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)+4>>2]|0)}if((c[e+76>>2]|0)==0){i=b;return}Fb[c[(c[(c[d>>2]|0)+8>>2]|0)+140>>2]&7](c[(c[d>>2]|0)+120>>2]|0,c[(c[d>>2]|0)+76>>2]|0);i=b;return}function zd(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;f=i;i=i+48|0;g=f+32|0;h=f+28|0;j=f+24|0;k=f+20|0;l=f+16|0;m=f+12|0;n=f+8|0;o=f+4|0;p=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;if((c[(c[g>>2]|0)+76>>2]|0)!=0?(c[(c[g>>2]|0)+132>>2]|0)>0:0){Fb[c[(c[(c[g>>2]|0)+8>>2]|0)+140>>2]&7](c[(c[g>>2]|0)+120>>2]|0,c[(c[g>>2]|0)+76>>2]|0);e=Ob[c[(c[(c[g>>2]|0)+8>>2]|0)+136>>2]&7](c[(c[g>>2]|0)+120>>2]|0,c[c[(c[g>>2]|0)+64>>2]>>2]|0)|0;c[(c[g>>2]|0)+76>>2]=e}a:do{if((c[k>>2]|0)!=0){c[m>>2]=1;do{c[m>>2]=c[m>>2]<<1;Qb[c[(c[(c[g>>2]|0)+8>>2]|0)+124>>2]&7](c[(c[g>>2]|0)+68>>2]|0,c[m>>2]|0,n,o);if((c[n>>2]|0)>(c[c[h>>2]>>2]|0)){break a}}while((c[o>>2]|0)<=(c[c[j>>2]>>2]|0))}else{c[m>>2]=(c[(c[g>>2]|0)+128>>2]|0)+1}}while(0);c[l>>2]=1;while(1){if(((c[m>>2]|0)-(c[l>>2]|0)|0)<=1){break}c[p>>2]=((c[m>>2]|0)+(c[l>>2]|0)|0)/2|0;Qb[c[(c[(c[g>>2]|0)+8>>2]|0)+124>>2]&7](c[(c[g>>2]|0)+68>>2]|0,c[p>>2]|0,n,o);if((c[n>>2]|0)<=(c[c[h>>2]>>2]|0)?(c[o>>2]|0)<=(c[c[j>>2]>>2]|0):0){c[l>>2]=c[p>>2];continue}c[m>>2]=c[p>>2]}c[(c[g>>2]|0)+132>>2]=c[l>>2];if((c[k>>2]|0)==0){q=c[g>>2]|0;Ad(q);r=c[g>>2]|0;s=r+136|0;t=c[s>>2]|0;u=c[h>>2]|0;c[u>>2]=t;v=c[g>>2]|0;w=v+140|0;x=c[w>>2]|0;y=c[j>>2]|0;c[y>>2]=x;i=f;return}c[(c[g>>2]|0)+128>>2]=c[(c[g>>2]|0)+132>>2];q=c[g>>2]|0;Ad(q);r=c[g>>2]|0;s=r+136|0;t=c[s>>2]|0;u=c[h>>2]|0;c[u>>2]=t;v=c[g>>2]|0;w=v+140|0;x=c[w>>2]|0;y=c[j>>2]|0;c[y>>2]=x;i=f;return}function Ad(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[(c[d>>2]|0)+132>>2]|0)<=0){i=b;return}Qb[c[(c[(c[d>>2]|0)+8>>2]|0)+124>>2]&7](c[(c[d>>2]|0)+68>>2]|0,c[(c[d>>2]|0)+132>>2]|0,(c[d>>2]|0)+136|0,(c[d>>2]|0)+140|0);Qb[c[(c[(c[d>>2]|0)+8>>2]|0)+128>>2]&7](c[(c[d>>2]|0)+120>>2]|0,c[(c[d>>2]|0)+76>>2]|0,c[(c[d>>2]|0)+68>>2]|0,c[(c[d>>2]|0)+132>>2]|0);i=b;return}function Bd(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;Eb[c[(c[(c[e>>2]|0)+8>>2]|0)+28>>2]&7](c[(c[e>>2]|0)+68>>2]|0);b=Jb[c[(c[(c[e>>2]|0)+8>>2]|0)+32>>2]&15](c[f>>2]|0)|0;c[(c[e>>2]|0)+68>>2]=b;i=d;return}function Cd(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[(c[d>>2]|0)+76>>2]|0)!=0){Fb[c[(c[(c[d>>2]|0)+8>>2]|0)+140>>2]&7](c[(c[d>>2]|0)+120>>2]|0,c[(c[d>>2]|0)+76>>2]|0)}a=Ob[c[(c[(c[d>>2]|0)+8>>2]|0)+136>>2]&7](c[(c[d>>2]|0)+120>>2]|0,c[c[(c[d>>2]|0)+64>>2]>>2]|0)|0;c[(c[d>>2]|0)+76>>2]=a;Ad(c[d>>2]|0);Dd(c[d>>2]|0);i=b;return}function Dd(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[(c[d>>2]|0)+120>>2]|0)==0){Ba(992,888,834,1008)}if((c[(c[d>>2]|0)+60>>2]|0)<=0){i=b;return}if((c[(c[d>>2]|0)+76>>2]|0)==0){i=b;return}qc(c[(c[d>>2]|0)+120>>2]|0);do{if(((c[(c[d>>2]|0)+84>>2]|0)!=0?+g[(c[d>>2]|0)+88>>2]>0.0:0)?+g[(c[d>>2]|0)+92>>2]<+g[(c[d>>2]|0)+88>>2]:0){if((c[(c[d>>2]|0)+104>>2]|0)!=0){Ib[c[(c[(c[d>>2]|0)+8>>2]|0)+144>>2]&1](c[(c[d>>2]|0)+120>>2]|0,c[(c[d>>2]|0)+76>>2]|0,c[(c[d>>2]|0)+84>>2]|0,c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[d>>2]|0)+104>>2]|0,c[(c[d>>2]|0)+80>>2]|0,+g[(c[d>>2]|0)+92>>2],+g[(c[d>>2]|0)+100>>2]);break}else{Ba(1024,888,840,1008)}}else{e=11}}while(0);if((e|0)==11){Ib[c[(c[(c[d>>2]|0)+8>>2]|0)+144>>2]&1](c[(c[d>>2]|0)+120>>2]|0,c[(c[d>>2]|0)+76>>2]|0,0,c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,1,c[(c[d>>2]|0)+80>>2]|0,0.0,+g[(c[d>>2]|0)+100>>2])}rc(c[(c[d>>2]|0)+120>>2]|0);i=b;return}function Ed(b){b=b|0;var d=0,e=0,f=0,h=0,j=0,k=0,l=0,m=0,n=0;d=i;i=i+48|0;e=d+20|0;f=d+16|0;h=d+24|0;j=d+12|0;k=d+8|0;l=d+4|0;m=d;c[e>>2]=b;Fd(c[e>>2]|0);yd(c[e>>2]|0);if((c[(c[e>>2]|0)+52>>2]|0)!=0){Ba(864,888,361,904)}b=(c[e>>2]|0)+48|0;if((c[(c[e>>2]|0)+48>>2]|0)==1){c[b>>2]=2}else{if((c[b>>2]|0)==0){c[(c[e>>2]|0)+48>>2]=2}else{a[h+15|0]=0;a[h]=49+(((qe(c[(c[e>>2]|0)+4>>2]|0,9)|0)&255)<<24>>24);c[j>>2]=1;while(1){n=c[e>>2]|0;if((c[j>>2]|0)>=15){break}b=48+(((qe(c[n+4>>2]|0,10)|0)&255)<<24>>24)&255;a[h+(c[j>>2]|0)|0]=b;c[j>>2]=(c[j>>2]|0)+1}td(c[n+40>>2]|0);n=vd(h)|0;c[(c[e>>2]|0)+40>>2]=n;if((c[(c[e>>2]|0)+72>>2]|0)!=0){Eb[c[(c[(c[e>>2]|0)+8>>2]|0)+28>>2]&7](c[(c[e>>2]|0)+72>>2]|0)}n=Jb[c[(c[(c[e>>2]|0)+8>>2]|0)+32>>2]&15](c[(c[e>>2]|0)+68>>2]|0)|0;c[(c[e>>2]|0)+72>>2]=n}td(c[(c[e>>2]|0)+32>>2]|0);td(c[(c[e>>2]|0)+36>>2]|0);td(c[(c[e>>2]|0)+44>>2]|0);c[(c[e>>2]|0)+44>>2]=0;n=c[(c[e>>2]|0)+40>>2]|0;c[f>>2]=oe(n,bg(c[(c[e>>2]|0)+40>>2]|0)|0)|0;n=Ab[c[(c[(c[e>>2]|0)+8>>2]|0)+52>>2]&3](c[(c[e>>2]|0)+72>>2]|0,c[f>>2]|0,(c[e>>2]|0)+44|0,(c[(c[e>>2]|0)+120>>2]|0)!=0|0)|0;c[(c[e>>2]|0)+32>>2]=n;c[(c[e>>2]|0)+36>>2]=0;re(c[f>>2]|0)}if((c[(c[e>>2]|0)+52>>2]|0)>=(c[(c[e>>2]|0)+56>>2]|0)){c[(c[e>>2]|0)+56>>2]=(c[(c[e>>2]|0)+52>>2]|0)+128;f=ud(c[(c[e>>2]|0)+64>>2]|0,(c[(c[e>>2]|0)+56>>2]|0)*12|0)|0;c[(c[e>>2]|0)+64>>2]=f}f=Kb[c[(c[(c[e>>2]|0)+8>>2]|0)+60>>2]&7](c[e>>2]|0,c[(c[e>>2]|0)+68>>2]|0,c[(c[e>>2]|0)+32>>2]|0)|0;c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+52>>2]|0)*12|0)>>2]=f;do{if((c[(c[(c[e>>2]|0)+8>>2]|0)+72>>2]|0)!=0?(c[(c[e>>2]|0)+44>>2]|0)!=0:0){c[l>>2]=0;c[m>>2]=Ab[c[(c[(c[e>>2]|0)+8>>2]|0)+76>>2]&3](c[c[(c[e>>2]|0)+64>>2]>>2]|0,c[c[(c[e>>2]|0)+64>>2]>>2]|0,c[(c[e>>2]|0)+44>>2]|0,l)|0;if((c[m>>2]|0)==0){Ba(920,888,442,904)}if((c[l>>2]|0)!=0){Ba(920,888,442,904)}c[k>>2]=Ob[c[(c[(c[e>>2]|0)+8>>2]|0)+116>>2]&7](c[c[(c[e>>2]|0)+64>>2]>>2]|0,c[m>>2]|0)|0;if((c[k>>2]|0)!=0){Eb[c[(c[(c[e>>2]|0)+8>>2]|0)+68>>2]&7](c[k>>2]|0);td(c[m>>2]|0);break}else{Ba(936,888,444,904)}}}while(0);c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+52>>2]|0)*12|0)+4>>2]=0;c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+52>>2]|0)*12|0)+8>>2]=0;m=(c[e>>2]|0)+52|0;c[m>>2]=(c[m>>2]|0)+1;c[(c[e>>2]|0)+60>>2]=1;m=Ob[c[(c[(c[e>>2]|0)+8>>2]|0)+136>>2]&7](c[(c[e>>2]|0)+120>>2]|0,c[c[(c[e>>2]|0)+64>>2]>>2]|0)|0;c[(c[e>>2]|0)+76>>2]=m;Ad(c[e>>2]|0);g[(c[e>>2]|0)+112>>2]=0.0;g[(c[e>>2]|0)+96>>2]=0.0;g[(c[e>>2]|0)+100>>2]=0.0;g[(c[e>>2]|0)+88>>2]=0.0;g[(c[e>>2]|0)+92>>2]=0.0;if((c[(c[e>>2]|0)+80>>2]|0)!=0){Eb[c[(c[(c[e>>2]|0)+8>>2]|0)+96>>2]&7](c[(c[e>>2]|0)+80>>2]|0)}m=Jb[c[(c[(c[e>>2]|0)+8>>2]|0)+92>>2]&15](c[c[(c[e>>2]|0)+64>>2]>>2]|0)|0;c[(c[e>>2]|0)+80>>2]=m;Gd(c[e>>2]|0);c[(c[e>>2]|0)+124>>2]=0;if((c[(c[e>>2]|0)+144>>2]|0)==0){i=d;return}Eb[c[(c[e>>2]|0)+144>>2]&7](c[(c[e>>2]|0)+148>>2]|0);i=d;return}function Fd(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[(c[d>>2]|0)+84>>2]|0)==0?!(+g[(c[d>>2]|0)+88>>2]!=0.0):0){i=b;return}Jd(c[d>>2]|0);Dd(c[d>>2]|0);i=b;return}function Gd(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[(c[(c[d>>2]|0)+8>>2]|0)+180>>2]|0)!=0){e=(Ob[c[(c[(c[d>>2]|0)+8>>2]|0)+184>>2]&7](c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[d>>2]|0)+80>>2]|0)|0)!=0}else{e=0}c[(c[d>>2]|0)+108>>2]=e&1;if(((c[(c[d>>2]|0)+108>>2]|0)==0?!(+g[(c[d>>2]|0)+96>>2]!=0.0):0)?!(+g[(c[d>>2]|0)+88>>2]!=0.0):0){Hc(c[c[d>>2]>>2]|0);i=b;return}Ic(c[c[d>>2]>>2]|0);i=b;return}function Hd(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;i=b;return(c[(c[d>>2]|0)+60>>2]|0)>1|0}function Id(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;i=b;return(c[(c[d>>2]|0)+60>>2]|0)<(c[(c[d>>2]|0)+52>>2]|0)|0}function Jd(a){a=a|0;var b=0,d=0,e=0,f=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;if(!((c[(c[d>>2]|0)+84>>2]|0)==0?(c[(c[d>>2]|0)+60>>2]|0)<=1:0)){f=3}do{if((f|0)==3){if(!((c[(c[d>>2]|0)+104>>2]|0)>0?(c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-1|0)*12|0)+8>>2]|0)==1:0)){if((c[(c[d>>2]|0)+104>>2]|0)>=0){break}if((c[(c[d>>2]|0)+60>>2]|0)>=(c[(c[d>>2]|0)+52>>2]|0)){break}if((c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+60>>2]|0)*12|0)+8>>2]|0)!=1){break}}a=c[d>>2]|0;if((c[(c[d>>2]|0)+84>>2]|0)!=0){h=c[a+84>>2]|0}else{h=c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[a+60>>2]|0)-2|0)*12|0)>>2]|0}if((c[(c[d>>2]|0)+84>>2]|0)!=0){j=c[(c[d>>2]|0)+104>>2]|0}else{j=1}g[e>>2]=+Pb[c[(c[(c[d>>2]|0)+8>>2]|0)+152>>2]&3](h,c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,j,c[(c[d>>2]|0)+80>>2]|0);if(+g[e>>2]>0.0){g[(c[d>>2]|0)+100>>2]=0.0;g[(c[d>>2]|0)+96>>2]=+g[e>>2]}}}while(0);if((c[(c[d>>2]|0)+84>>2]|0)==0){k=c[d>>2]|0;l=k+84|0;c[l>>2]=0;m=c[d>>2]|0;n=m+88|0;g[n>>2]=0.0;o=c[d>>2]|0;p=o+92|0;g[p>>2]=0.0;q=c[d>>2]|0;r=q+104|0;c[r>>2]=0;s=c[d>>2]|0;Gd(s);i=b;return}Eb[c[(c[(c[d>>2]|0)+8>>2]|0)+68>>2]&7](c[(c[d>>2]|0)+84>>2]|0);k=c[d>>2]|0;l=k+84|0;c[l>>2]=0;m=c[d>>2]|0;n=m+88|0;g[n>>2]=0.0;o=c[d>>2]|0;p=o+92|0;g[p>>2]=0.0;q=c[d>>2]|0;r=q+104|0;c[r>>2]=0;s=c[d>>2]|0;Gd(s);i=b;return}function Kd(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;if((c[(c[d>>2]|0)+60>>2]|0)<1){Ba(944,888,552,968)}if((c[(c[d>>2]|0)+60>>2]|0)==1){i=b;return}c[e>>2]=Kb[c[(c[(c[d>>2]|0)+8>>2]|0)+60>>2]&7](c[d>>2]|0,c[(c[d>>2]|0)+68>>2]|0,c[(c[d>>2]|0)+32>>2]|0)|0;Fd(c[d>>2]|0);Ld(c[d>>2]|0);if((c[(c[d>>2]|0)+52>>2]|0)>=(c[(c[d>>2]|0)+56>>2]|0)){c[(c[d>>2]|0)+56>>2]=(c[(c[d>>2]|0)+52>>2]|0)+128;a=ud(c[(c[d>>2]|0)+64>>2]|0,(c[(c[d>>2]|0)+56>>2]|0)*12|0)|0;c[(c[d>>2]|0)+64>>2]=a}c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)>>2]=c[e>>2];e=vd(c[(c[d>>2]|0)+32>>2]|0)|0;c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)+4>>2]=e;c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)+8>>2]=3;e=(c[d>>2]|0)+52|0;a=(c[e>>2]|0)+1|0;c[e>>2]=a;c[(c[d>>2]|0)+60>>2]=a;if((c[(c[d>>2]|0)+80>>2]|0)!=0){Lb[c[(c[(c[d>>2]|0)+8>>2]|0)+108>>2]&3](c[(c[d>>2]|0)+80>>2]|0,c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-2|0)*12|0)>>2]|0,c[(c[(c[d>>2]|0)+64>>2]|0)+(((c[(c[d>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0)}g[(c[d>>2]|0)+96>>2]=0.0;g[(c[d>>2]|0)+100>>2]=0.0;Jd(c[d>>2]|0);Dd(c[d>>2]|0);Gd(c[d>>2]|0);i=b;return}function Ld(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b;c[d>>2]=a;while(1){if((c[(c[d>>2]|0)+52>>2]|0)<=(c[(c[d>>2]|0)+60>>2]|0)){break}a=c[(c[(c[d>>2]|0)+8>>2]|0)+68>>2]|0;e=(c[d>>2]|0)+52|0;f=(c[e>>2]|0)+ -1|0;c[e>>2]=f;Eb[a&7](c[(c[(c[d>>2]|0)+64>>2]|0)+(f*12|0)>>2]|0);if((c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)+4>>2]|0)==0){continue}td(c[(c[(c[d>>2]|0)+64>>2]|0)+((c[(c[d>>2]|0)+52>>2]|0)*12|0)+4>>2]|0)}i=b;return}function Md(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0;f=i;i=i+32|0;g=f+20|0;h=f+16|0;j=f+12|0;k=f+8|0;l=f+4|0;m=f;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=1;if(!(((c[l>>2]|0)-515|0)>>>0<=2)?!(((c[l>>2]|0)-518|0)>>>0<=2):0){if(((c[l>>2]|0)-512|0)>>>0<=2?(c[(c[h>>2]|0)+124>>2]|0)!=0:0){e=c[m>>2]|0;if((c[(c[(c[h>>2]|0)+8>>2]|0)+188>>2]&1<<(((c[(c[h>>2]|0)+124>>2]|0)-512|0)*3|0)+(c[l>>2]|0)-512|0)!=0){c[g>>2]=e;n=c[g>>2]|0;i=f;return n|0}if((e|0)!=0){o=(Nd(c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,(c[(c[h>>2]|0)+124>>2]|0)+6|0)|0)!=0}else{o=0}c[m>>2]=o&1}}else{p=3}do{if((p|0)==3){if((c[(c[h>>2]|0)+124>>2]|0)==0){c[g>>2]=c[m>>2];n=c[g>>2]|0;i=f;return n|0}o=c[(c[h>>2]|0)+124>>2]|0;if(((c[l>>2]|0)-515|0)>>>0<=2){c[l>>2]=o+3;break}else{c[l>>2]=o+6;break}}}while(0);if((c[l>>2]|0)==10|(c[l>>2]|0)==13){c[l>>2]=525}if((c[l>>2]|0)==32){c[l>>2]=526}if((c[l>>2]|0)==127){c[l>>2]=8}if((c[m>>2]|0)!=0){q=(Nd(c[h>>2]|0,c[j>>2]|0,c[k>>2]|0,c[l>>2]|0)|0)!=0}else{q=0}c[m>>2]=q&1;if(!(((c[l>>2]|0)-518|0)>>>0<=2)){if(((c[l>>2]|0)-512|0)>>>0<=2){c[(c[h>>2]|0)+124>>2]=c[l>>2]}}else{c[(c[h>>2]|0)+124>>2]=0}c[g>>2]=c[m>>2];n=c[g>>2]|0;i=f;return n|0}function Nd(b,d,e,f){b=b|0;d=d|0;e=e|0;f=f|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0;h=i;i=i+48|0;j=h+40|0;k=h+36|0;l=h+32|0;m=h+28|0;n=h+24|0;o=h+20|0;p=h+16|0;q=h+12|0;r=h+8|0;s=h+4|0;t=h;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=Jb[c[(c[(c[j>>2]|0)+8>>2]|0)+64>>2]&15](c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0)|0;c[o>>2]=1;c[p>>2]=0;c[q>>2]=1;c[t>>2]=Gb[c[(c[(c[j>>2]|0)+8>>2]|0)+112>>2]&1](c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[j>>2]|0)+80>>2]|0,c[(c[j>>2]|0)+76>>2]|0,c[k>>2]|0,c[l>>2]|0,c[m>>2]|0)|0;do{if((c[t>>2]|0)!=0){l=c[j>>2]|0;do{if((a[c[t>>2]|0]|0)!=0){c[s>>2]=Ob[c[(c[l+8>>2]|0)+116>>2]&7](c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[t>>2]|0)|0;if((c[s>>2]|0)!=0){break}else{Ba(1528,888,629,1544)}}else{c[s>>2]=c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[l+60>>2]|0)-1|0)*12|0)>>2]}}while(0);if((c[s>>2]|0)==(c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0)){Dd(c[j>>2]|0);Gd(c[j>>2]|0);break}if((c[s>>2]|0)!=0){Fd(c[j>>2]|0);Ld(c[j>>2]|0);if((c[(c[j>>2]|0)+52>>2]|0)>=(c[(c[j>>2]|0)+56>>2]|0)){c[(c[j>>2]|0)+56>>2]=(c[(c[j>>2]|0)+52>>2]|0)+128;l=ud(c[(c[j>>2]|0)+64>>2]|0,(c[(c[j>>2]|0)+56>>2]|0)*12|0)|0;c[(c[j>>2]|0)+64>>2]=l}if((c[t>>2]|0)==0){Ba(1576,888,645,1544)}c[(c[(c[j>>2]|0)+64>>2]|0)+((c[(c[j>>2]|0)+52>>2]|0)*12|0)>>2]=c[s>>2];c[(c[(c[j>>2]|0)+64>>2]|0)+((c[(c[j>>2]|0)+52>>2]|0)*12|0)+4>>2]=c[t>>2];c[(c[(c[j>>2]|0)+64>>2]|0)+((c[(c[j>>2]|0)+52>>2]|0)*12|0)+8>>2]=1;l=(c[j>>2]|0)+52|0;k=(c[l>>2]|0)+1|0;c[l>>2]=k;c[(c[j>>2]|0)+60>>2]=k;c[(c[j>>2]|0)+104>>2]=1;if((c[(c[j>>2]|0)+80>>2]|0)!=0){Lb[c[(c[(c[j>>2]|0)+8>>2]|0)+108>>2]&3](c[(c[j>>2]|0)+80>>2]|0,c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-2|0)*12|0)>>2]|0,c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0);u=27}else{u=27}}}else{if((c[m>>2]|0)==110|(c[m>>2]|0)==78|(c[m>>2]|0)==14){Ed(c[j>>2]|0);Dd(c[j>>2]|0);break}if((c[m>>2]|0)==117|(c[m>>2]|0)==85|(c[m>>2]|0)==26|(c[m>>2]|0)==31){Fd(c[j>>2]|0);c[o>>2]=c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)+8>>2];c[p>>2]=1;if((be(c[j>>2]|0)|0)!=0){u=27;break}else{break}}if((c[m>>2]|0)==114|(c[m>>2]|0)==82|(c[m>>2]|0)==18|(c[m>>2]|0)==25){Fd(c[j>>2]|0);if((ce(c[j>>2]|0)|0)!=0){u=27;break}else{break}}if((c[m>>2]|0)==19?(c[(c[(c[j>>2]|0)+8>>2]|0)+72>>2]|0)!=0:0){if(($d(c[j>>2]|0)|0)!=0){break}else{u=27;break}}if((c[m>>2]|0)==113|(c[m>>2]|0)==81|(c[m>>2]|0)==17){c[q>>2]=0}}}while(0);if((u|0)==27){if((c[p>>2]|0)==0){c[o>>2]=c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)+8>>2]}do{if((c[o>>2]|0)!=1){if((c[o>>2]|0)==2?(c[(c[(c[j>>2]|0)+8>>2]|0)+188>>2]&512|0)!=0:0){u=33;break}g[r>>2]=0.0}else{u=33}}while(0);if((u|0)==33){g[r>>2]=+Pb[c[(c[(c[j>>2]|0)+8>>2]|0)+148>>2]&3](c[n>>2]|0,c[(c[(c[j>>2]|0)+64>>2]|0)+(((c[(c[j>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[j>>2]|0)+104>>2]|0,c[(c[j>>2]|0)+80>>2]|0)}c[(c[j>>2]|0)+84>>2]=c[n>>2];c[n>>2]=0;if(+g[r>>2]>0.0){g[(c[j>>2]|0)+88>>2]=+g[r>>2]}else{g[(c[j>>2]|0)+88>>2]=0.0;Jd(c[j>>2]|0)}g[(c[j>>2]|0)+92>>2]=0.0;Dd(c[j>>2]|0);Gd(c[j>>2]|0)}if((c[n>>2]|0)==0){v=c[q>>2]|0;i=h;return v|0}Eb[c[(c[(c[j>>2]|0)+8>>2]|0)+68>>2]&7](c[n>>2]|0);v=c[q>>2]|0;i=h;return v|0}function Od(a,b){a=a|0;b=+b;var d=0,e=0,f=0,h=0,j=0,k=0,l=0,m=0,n=0;d=i;i=i+16|0;e=d+12|0;f=d+8|0;h=d+4|0;j=d;c[e>>2]=a;g[f>>2]=b;if(+g[(c[e>>2]|0)+88>>2]>0.0){k=1}else{k=+g[(c[e>>2]|0)+96>>2]>0.0}c[h>>2]=k&1;k=(c[e>>2]|0)+92|0;g[k>>2]=+g[k>>2]+ +g[f>>2];if(!((!(+g[(c[e>>2]|0)+92>>2]>=+g[(c[e>>2]|0)+88>>2])?!(+g[(c[e>>2]|0)+88>>2]==0.0):0)?(c[(c[e>>2]|0)+84>>2]|0)!=0:0)){l=6}if((l|0)==6?+g[(c[e>>2]|0)+88>>2]>0.0:0){Jd(c[e>>2]|0)}l=(c[e>>2]|0)+100|0;g[l>>2]=+g[l>>2]+ +g[f>>2];if(!(!(+g[(c[e>>2]|0)+100>>2]>=+g[(c[e>>2]|0)+96>>2])?!(+g[(c[e>>2]|0)+96>>2]==0.0):0)){g[(c[e>>2]|0)+96>>2]=0.0;g[(c[e>>2]|0)+100>>2]=0.0}if((c[h>>2]|0)!=0){Dd(c[e>>2]|0)}if((c[(c[e>>2]|0)+108>>2]|0)==0){m=c[e>>2]|0;Gd(m);i=d;return}g[j>>2]=+g[(c[e>>2]|0)+112>>2];h=(c[e>>2]|0)+112|0;g[h>>2]=+g[h>>2]+ +g[f>>2];if((~~+g[j>>2]|0)==(~~+g[(c[e>>2]|0)+112>>2]|0)){m=c[e>>2]|0;Gd(m);i=d;return}if((c[(c[e>>2]|0)+116>>2]|0)!=0){n=c[(c[e>>2]|0)+116>>2]|0}else{n=1040}sc(c[(c[e>>2]|0)+120>>2]|0,n);m=c[e>>2]|0;Gd(m);i=d;return}function Pd(b,e){b=b|0;e=e|0;var f=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;f=i;i=i+144|0;h=f;j=f+48|0;k=f+44|0;l=f+40|0;m=f+36|0;n=f+56|0;o=f+32|0;p=f+28|0;q=f+24|0;r=f+20|0;s=f+16|0;t=f+12|0;c[j>>2]=b;c[k>>2]=e;c[l>>2]=Ob[c[(c[(c[j>>2]|0)+8>>2]|0)+132>>2]&7](c[c[j>>2]>>2]|0,c[k>>2]|0)|0;c[m>>2]=0;while(1){if((c[m>>2]|0)>=(c[c[k>>2]>>2]|0)){break}e=c[m>>2]|0;c[h>>2]=c[c[(c[j>>2]|0)+8>>2]>>2];c[h+4>>2]=e;ab(n|0,1048,h|0)|0;c[t>>2]=0;c[s>>2]=0;while(1){if((a[n+(c[s>>2]|0)|0]|0)==0){break}if((Ya(d[n+(c[s>>2]|0)|0]|0)|0)==0){e=(db(d[n+(c[s>>2]|0)|0]|0)|0)&255;b=c[t>>2]|0;c[t>>2]=b+1;a[n+b|0]=e}c[s>>2]=(c[s>>2]|0)+1}a[n+(c[t>>2]|0)|0]=0;e=$a(n|0)|0;c[o>>2]=e;if((e|0)!=0?(e=c[o>>2]|0,c[h>>2]=p,c[h+4>>2]=q,c[h+8>>2]=r,(Ia(e|0,1064,h|0)|0)==3):0){g[(c[l>>2]|0)+(((c[m>>2]|0)*3|0)+0<<2)>>2]=+((c[p>>2]|0)>>>0)/255.0;g[(c[l>>2]|0)+(((c[m>>2]|0)*3|0)+1<<2)>>2]=+((c[q>>2]|0)>>>0)/255.0;g[(c[l>>2]|0)+(((c[m>>2]|0)*3|0)+2<<2)>>2]=+((c[r>>2]|0)>>>0)/255.0}c[m>>2]=(c[m>>2]|0)+1}i=f;return c[l>>2]|0}function Qd(b){b=b|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;e=i;i=i+128|0;f=e;g=e+40|0;h=e+36|0;j=e+32|0;k=e+48|0;l=e+28|0;m=e+24|0;n=e+20|0;o=e+16|0;p=e+12|0;q=e+8|0;r=e+4|0;c[g>>2]=b;a:do{if((c[(c[g>>2]|0)+24>>2]|0)==0){while(1){if((Kb[c[(c[(c[g>>2]|0)+8>>2]|0)+16>>2]&7](c[(c[g>>2]|0)+24>>2]|0,h,j)|0)==0){break a}if((c[(c[g>>2]|0)+28>>2]|0)<=(c[(c[g>>2]|0)+24>>2]|0)){c[(c[g>>2]|0)+28>>2]=(c[(c[g>>2]|0)+24>>2]|0)+10;b=ud(c[(c[g>>2]|0)+12>>2]|0,c[(c[g>>2]|0)+28>>2]<<2)|0;c[(c[g>>2]|0)+12>>2]=b;b=ud(c[(c[g>>2]|0)+16>>2]|0,c[(c[g>>2]|0)+28>>2]<<2)|0;c[(c[g>>2]|0)+16>>2]=b;b=ud(c[(c[g>>2]|0)+20>>2]|0,c[(c[g>>2]|0)+28>>2]<<2)|0;c[(c[g>>2]|0)+20>>2]=b}c[(c[(c[g>>2]|0)+12>>2]|0)+(c[(c[g>>2]|0)+24>>2]<<2)>>2]=c[j>>2];c[(c[(c[g>>2]|0)+16>>2]|0)+(c[(c[g>>2]|0)+24>>2]<<2)>>2]=c[h>>2];b=Ob[c[(c[(c[g>>2]|0)+8>>2]|0)+24>>2]&7](c[j>>2]|0,1)|0;c[(c[(c[g>>2]|0)+20>>2]|0)+(c[(c[g>>2]|0)+24>>2]<<2)>>2]=b;b=(c[g>>2]|0)+24|0;c[b>>2]=(c[b>>2]|0)+1}}}while(0);c[f>>2]=c[c[(c[g>>2]|0)+8>>2]>>2];ab(k|0,1080,f|0)|0;c[o>>2]=0;c[n>>2]=0;while(1){if((a[k+(c[n>>2]|0)|0]|0)==0){break}if((Ya(d[k+(c[n>>2]|0)|0]|0)|0)==0){f=(db(d[k+(c[n>>2]|0)|0]|0)|0)&255;j=c[o>>2]|0;c[o>>2]=j+1;a[k+j|0]=f}c[n>>2]=(c[n>>2]|0)+1}a[k+(c[o>>2]|0)|0]=0;o=$a(k|0)|0;c[l>>2]=o;if((o|0)==0){s=c[g>>2]|0;t=s+24|0;u=c[t>>2]|0;i=e;return u|0}o=vd(c[l>>2]|0)|0;c[l>>2]=o;c[m>>2]=o;while(1){if((a[c[m>>2]|0]|0)==0){break}c[p>>2]=c[m>>2];while(1){if((a[c[m>>2]|0]|0)!=0){v=(a[c[m>>2]|0]|0)!=58}else{v=0}w=c[m>>2]|0;if(!v){break}c[m>>2]=w+1}if((a[w]|0)!=0){o=c[m>>2]|0;c[m>>2]=o+1;a[o]=0}c[q>>2]=c[m>>2];while(1){if((a[c[m>>2]|0]|0)!=0){x=(a[c[m>>2]|0]|0)!=58}else{x=0}y=c[m>>2]|0;if(!x){break}c[m>>2]=y+1}if((a[y]|0)!=0){o=c[m>>2]|0;c[m>>2]=o+1;a[o]=0}c[r>>2]=Db[c[(c[(c[g>>2]|0)+8>>2]|0)+12>>2]&1]()|0;Fb[c[(c[(c[g>>2]|0)+8>>2]|0)+20>>2]&7](c[r>>2]|0,c[q>>2]|0);o=(Ob[c[(c[(c[g>>2]|0)+8>>2]|0)+48>>2]&7](c[r>>2]|0,1)|0)!=0;k=c[g>>2]|0;if(o){Eb[c[(c[k+8>>2]|0)+28>>2]&7](c[r>>2]|0);continue}if((c[k+28>>2]|0)<=(c[(c[g>>2]|0)+24>>2]|0)){c[(c[g>>2]|0)+28>>2]=(c[(c[g>>2]|0)+24>>2]|0)+10;k=ud(c[(c[g>>2]|0)+12>>2]|0,c[(c[g>>2]|0)+28>>2]<<2)|0;c[(c[g>>2]|0)+12>>2]=k;k=ud(c[(c[g>>2]|0)+16>>2]|0,c[(c[g>>2]|0)+28>>2]<<2)|0;c[(c[g>>2]|0)+16>>2]=k;k=ud(c[(c[g>>2]|0)+20>>2]|0,c[(c[g>>2]|0)+28>>2]<<2)|0;c[(c[g>>2]|0)+20>>2]=k}c[(c[(c[g>>2]|0)+12>>2]|0)+(c[(c[g>>2]|0)+24>>2]<<2)>>2]=c[r>>2];k=vd(c[p>>2]|0)|0;c[(c[(c[g>>2]|0)+16>>2]|0)+(c[(c[g>>2]|0)+24>>2]<<2)>>2]=k;k=Ob[c[(c[(c[g>>2]|0)+8>>2]|0)+24>>2]&7](c[r>>2]|0,1)|0;c[(c[(c[g>>2]|0)+20>>2]|0)+(c[(c[g>>2]|0)+24>>2]<<2)>>2]=k;k=(c[g>>2]|0)+24|0;c[k>>2]=(c[k>>2]|0)+1}td(c[l>>2]|0);s=c[g>>2]|0;t=s+24|0;u=c[t>>2]|0;i=e;return u|0}function Rd(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0;f=i;i=i+16|0;g=f+12|0;h=f+8|0;j=f+4|0;k=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;if((c[h>>2]|0)<0){Ba(1096,888,1021,1128)}if((c[h>>2]|0)<(c[(c[g>>2]|0)+24>>2]|0)){c[c[j>>2]>>2]=c[(c[(c[g>>2]|0)+16>>2]|0)+(c[h>>2]<<2)>>2];c[c[k>>2]>>2]=c[(c[(c[g>>2]|0)+12>>2]|0)+(c[h>>2]<<2)>>2];i=f;return}else{Ba(1096,888,1021,1128)}}function Sd(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0;b=i;i=i+16|0;d=b+12|0;e=b+8|0;f=b+4|0;g=b;c[d>>2]=a;c[e>>2]=Ob[c[(c[(c[d>>2]|0)+8>>2]|0)+24>>2]&7](c[(c[d>>2]|0)+68>>2]|0,1)|0;c[g>>2]=-1;c[f>>2]=0;while(1){if((c[f>>2]|0)>=(c[(c[d>>2]|0)+24>>2]|0)){h=6;break}a=($f(c[e>>2]|0,c[(c[(c[d>>2]|0)+20>>2]|0)+(c[f>>2]<<2)>>2]|0)|0)!=0;j=c[f>>2]|0;if(!a){break}c[f>>2]=j+1}if((h|0)==6){k=c[e>>2]|0;td(k);l=c[g>>2]|0;i=b;return l|0}c[g>>2]=j;k=c[e>>2]|0;td(k);l=c[g>>2]|0;i=b;return l|0}function Td(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;i=b;return c[(c[(c[d>>2]|0)+8>>2]|0)+176>>2]|0}function Ud(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0;e=i;i=i+16|0;f=e+8|0;g=e+4|0;h=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;c[(c[f>>2]|0)+144>>2]=c[g>>2];c[(c[f>>2]|0)+148>>2]=c[h>>2];i=e;return}function Vd(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;f=i;i=i+48|0;g=f;h=f+40|0;j=f+36|0;k=f+32|0;l=f+28|0;m=f+24|0;n=f+20|0;o=f+16|0;p=f+12|0;q=f+44|0;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;if((c[l>>2]|0)==0){Ba(1152,888,1069,1168)}c[m>>2]=sd(40+(bg(c[c[(c[j>>2]|0)+8>>2]>>2]|0)|0)|0)|0;e=c[k>>2]|0;if((e|0)==2|(e|0)==1){d=c[m>>2]|0;if((c[(c[j>>2]|0)+72>>2]|0)==0){td(d);c[h>>2]=0;r=c[h>>2]|0;i=f;return r|0}b=(c[k>>2]|0)==1?1232:1240;c[g>>2]=c[c[(c[j>>2]|0)+8>>2]>>2];c[g+4>>2]=b;ab(d|0,1216,g|0)|0;c[c[l>>2]>>2]=c[m>>2];c[p>>2]=sd(32)|0;c[(c[p>>2]|0)+4>>2]=0;d=c[p>>2]|0;if((c[k>>2]|0)==1){c[d>>2]=1248}else{c[d>>2]=1272}c[(c[p>>2]|0)+12>>2]=0;c[n>>2]=Ob[c[(c[(c[j>>2]|0)+8>>2]|0)+24>>2]&7](c[(c[j>>2]|0)+72>>2]|0,(c[k>>2]|0)==1|0)|0;if((c[n>>2]|0)==0){Ba(1280,888,1105,1168)}d=c[j>>2]|0;if((c[k>>2]|0)==2){if((c[d+32>>2]|0)!=0){s=c[(c[j>>2]|0)+32>>2]|0}else{s=1040}c[o>>2]=s;a[q]=58}else{if((c[d+40>>2]|0)!=0){t=c[(c[j>>2]|0)+40>>2]|0}else{t=1040}c[o>>2]=t;a[q]=35}t=bg(c[n>>2]|0)|0;d=sd(t+(bg(c[o>>2]|0)|0)+2|0)|0;c[(c[p>>2]|0)+8>>2]=d;d=c[(c[p>>2]|0)+8>>2]|0;t=a[q]|0;q=c[o>>2]|0;c[g>>2]=c[n>>2];c[g+4>>2]=t;c[g+8>>2]=q;ab(d|0,1288,g|0)|0;td(c[n>>2]|0);c[(c[p>>2]|0)+20>>2]=3;c[(c[p>>2]|0)+24>>2]=0;c[(c[p>>2]|0)+16>>2]=0;c[(c[p>>2]|0)+28>>2]=0;c[h>>2]=c[p>>2];r=c[h>>2]|0;i=f;return r|0}else if((e|0)==0){e=c[m>>2]|0;c[g>>2]=c[c[(c[j>>2]|0)+8>>2]>>2];ab(e|0,1192,g|0)|0;c[c[l>>2]>>2]=c[m>>2];c[h>>2]=Jb[c[(c[(c[j>>2]|0)+8>>2]|0)+40>>2]&15](c[(c[j>>2]|0)+68>>2]|0)|0;r=c[h>>2]|0;i=f;return r|0}else{Ba(1296,888,1124,1168)}return 0}function Wd(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+4|0;f=d;c[e>>2]=a;c[f>>2]=b;b=Xd(c[e>>2]|0,c[f>>2]|0,0)|0;i=d;return b|0}function Xd(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0;f=i;i=i+64|0;g=f+52|0;h=f+48|0;j=f+44|0;k=f+40|0;l=f+36|0;m=f+32|0;n=f+28|0;o=f+24|0;p=f+20|0;q=f+16|0;r=f+12|0;s=f+8|0;t=f+4|0;u=f;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[o>>2]=Sf(c[j>>2]|0,35)|0;c[n>>2]=Sf(c[j>>2]|0,58)|0;do{if((c[n>>2]|0)!=0){if((c[o>>2]|0)!=0?!((c[n>>2]|0)>>>0<(c[o>>2]|0)>>>0):0){v=5;break}e=c[n>>2]|0;c[n>>2]=e+1;a[e]=0;c[m>>2]=c[j>>2];c[o>>2]=0}else{v=5}}while(0);a:do{if((v|0)==5){do{if((c[o>>2]|0)!=0){if((c[n>>2]|0)!=0?!((c[o>>2]|0)>>>0<(c[n>>2]|0)>>>0):0){break}e=c[o>>2]|0;c[o>>2]=e+1;a[e]=0;c[m>>2]=c[j>>2];c[n>>2]=0;break a}}while(0);if((c[k>>2]|0)==1){c[o>>2]=c[j>>2];c[n>>2]=0;c[m>>2]=0;break}e=c[j>>2]|0;if((c[k>>2]|0)==2){c[n>>2]=e;c[o>>2]=0;c[m>>2]=0;break}else{c[m>>2]=e;c[n>>2]=0;c[o>>2]=0;break}}}while(0);c[s>>2]=0;c[r>>2]=0;c[q>>2]=0;c[p>>2]=0;if((c[m>>2]|0)!=0){k=c[(c[h>>2]|0)+8>>2]|0;if((c[n>>2]|0)!=0){c[p>>2]=Jb[c[k+32>>2]&15](c[(c[h>>2]|0)+68>>2]|0)|0}else{c[p>>2]=Db[c[k+12>>2]&1]()|0}Fb[c[(c[(c[h>>2]|0)+8>>2]|0)+20>>2]&7](c[p>>2]|0,c[m>>2]|0);c[l>>2]=Ob[c[(c[(c[h>>2]|0)+8>>2]|0)+48>>2]&7](c[p>>2]|0,(c[n>>2]|0)==0|0)|0;m=c[h>>2]|0;if((c[l>>2]|0)!=0){Eb[c[(c[m+8>>2]|0)+28>>2]&7](c[p>>2]|0);c[g>>2]=c[l>>2];w=c[g>>2]|0;i=f;return w|0}c[r>>2]=c[m+72>>2];c[s>>2]=c[(c[h>>2]|0)+68>>2];if((c[o>>2]|0)==0?(c[n>>2]|0)==0:0){c[q>>2]=Jb[c[(c[(c[h>>2]|0)+8>>2]|0)+32>>2]&15](c[p>>2]|0)|0}else{c[q>>2]=Jb[c[(c[(c[h>>2]|0)+8>>2]|0)+32>>2]&15](c[(c[h>>2]|0)+68>>2]|0)|0;c[u>>2]=Ob[c[(c[(c[h>>2]|0)+8>>2]|0)+24>>2]&7](c[p>>2]|0,0)|0;Fb[c[(c[(c[h>>2]|0)+8>>2]|0)+20>>2]&7](c[q>>2]|0,c[u>>2]|0);td(c[u>>2]|0)}c[t>>2]=1}else{c[p>>2]=c[(c[h>>2]|0)+72>>2];c[q>>2]=c[(c[h>>2]|0)+68>>2];c[t>>2]=0}if((c[n>>2]|0)!=0?(c[l>>2]=Ob[c[(c[(c[h>>2]|0)+8>>2]|0)+56>>2]&7](c[q>>2]|0,c[n>>2]|0)|0,(c[l>>2]|0)!=0):0){if((c[t>>2]|0)!=0){if((c[p>>2]|0)!=0){Eb[c[(c[(c[h>>2]|0)+8>>2]|0)+28>>2]&7](c[p>>2]|0)}if((c[q>>2]|0)!=0){Eb[c[(c[(c[h>>2]|0)+8>>2]|0)+28>>2]&7](c[q>>2]|0)}}c[g>>2]=c[l>>2];w=c[g>>2]|0;i=f;return w|0}c[(c[h>>2]|0)+68>>2]=c[q>>2];c[(c[h>>2]|0)+72>>2]=c[p>>2];if((c[r>>2]|0)!=0){Eb[c[(c[(c[h>>2]|0)+8>>2]|0)+28>>2]&7](c[r>>2]|0)}if((c[s>>2]|0)!=0){Eb[c[(c[(c[h>>2]|0)+8>>2]|0)+28>>2]&7](c[s>>2]|0)}td(c[(c[h>>2]|0)+32>>2]|0);td(c[(c[h>>2]|0)+36>>2]|0);c[(c[h>>2]|0)+36>>2]=0;c[(c[h>>2]|0)+32>>2]=0;td(c[(c[h>>2]|0)+40>>2]|0);c[(c[h>>2]|0)+40>>2]=0;if((c[n>>2]|0)!=0){s=vd(c[n>>2]|0)|0;c[(c[h>>2]|0)+32>>2]=s;c[(c[h>>2]|0)+48>>2]=1;td(c[(c[h>>2]|0)+44>>2]|0);c[(c[h>>2]|0)+44>>2]=0}if((c[o>>2]|0)!=0){s=vd(c[o>>2]|0)|0;c[(c[h>>2]|0)+40>>2]=s;c[(c[h>>2]|0)+48>>2]=0}c[g>>2]=0;w=c[g>>2]|0;i=f;return w|0}function Yd(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0;b=i;i=i+32|0;d=b;e=b+16|0;f=b+12|0;g=b+8|0;c[e>>2]=a;c[f>>2]=Ob[c[(c[(c[e>>2]|0)+8>>2]|0)+24>>2]&7](c[(c[e>>2]|0)+72>>2]|0,0)|0;if((c[f>>2]|0)==0){Ba(1280,888,1310,1320)}if((c[(c[e>>2]|0)+32>>2]|0)!=0){a=bg(c[f>>2]|0)|0;c[g>>2]=sd(a+(bg(c[(c[e>>2]|0)+32>>2]|0)|0)+2|0)|0;a=c[g>>2]|0;h=c[(c[e>>2]|0)+32>>2]|0;c[d>>2]=c[f>>2];c[d+4>>2]=h;ab(a|0,1360,d|0)|0;td(c[f>>2]|0);i=b;return c[g>>2]|0}else{Ba(1344,888,1311,1320)}return 0}function Zd(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0;b=i;i=i+32|0;d=b;e=b+20|0;f=b+16|0;g=b+12|0;h=b+8|0;c[f>>2]=a;if((c[(c[f>>2]|0)+40>>2]|0)==0){c[e>>2]=0;j=c[e>>2]|0;i=b;return j|0}c[g>>2]=Ob[c[(c[(c[f>>2]|0)+8>>2]|0)+24>>2]&7](c[(c[f>>2]|0)+72>>2]|0,1)|0;if((c[g>>2]|0)==0){Ba(1280,888,1326,1368)}a=bg(c[g>>2]|0)|0;c[h>>2]=sd(a+(bg(c[(c[f>>2]|0)+40>>2]|0)|0)+2|0)|0;a=c[h>>2]|0;k=c[(c[f>>2]|0)+40>>2]|0;c[d>>2]=c[g>>2];c[d+4>>2]=k;ab(a|0,1392,d|0)|0;td(c[g>>2]|0);c[e>>2]=c[h>>2];j=c[e>>2]|0;i=b;return j|0}function _d(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0;e=i;i=i+32|0;f=e+20|0;g=e+16|0;h=e+12|0;j=e+8|0;k=e+4|0;l=e;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;d=c[h>>2]|0;do{if((d|0)==2|(d|0)==1){c[k>>2]=Xd(c[g>>2]|0,c[(c[j>>2]|0)+8>>2]|0,(c[h>>2]|0)==1?1:2)|0;if((c[k>>2]|0)!=0){c[f>>2]=c[k>>2];m=c[f>>2]|0;i=e;return m|0}}else if((d|0)==0){c[l>>2]=Jb[c[(c[(c[g>>2]|0)+8>>2]|0)+44>>2]&15](c[j>>2]|0)|0;c[k>>2]=Ob[c[(c[(c[g>>2]|0)+8>>2]|0)+48>>2]&7](c[l>>2]|0,1)|0;b=c[(c[(c[g>>2]|0)+8>>2]|0)+28>>2]|0;if((c[k>>2]|0)==0){Eb[b&7](c[(c[g>>2]|0)+68>>2]|0);c[(c[g>>2]|0)+68>>2]=c[l>>2];break}Eb[b&7](c[l>>2]|0);c[f>>2]=c[k>>2];m=c[f>>2]|0;i=e;return m|0}}while(0);c[f>>2]=0;m=c[f>>2]|0;i=e;return m|0}function $d(a){a=a|0;var b=0,d=0,e=0,f=0,h=0,j=0,k=0,l=0.0;b=i;i=i+32|0;d=b+16|0;e=b+12|0;f=b+8|0;h=b+4|0;j=b;c[e>>2]=a;if((c[(c[(c[e>>2]|0)+8>>2]|0)+72>>2]|0)==0){c[d>>2]=1400;k=c[d>>2]|0;i=b;return k|0}if((c[(c[e>>2]|0)+60>>2]|0)<1){c[d>>2]=1448;k=c[d>>2]|0;i=b;return k|0}c[h>>2]=0;c[j>>2]=Ab[c[(c[(c[e>>2]|0)+8>>2]|0)+76>>2]&3](c[c[(c[e>>2]|0)+64>>2]>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[e>>2]|0)+44>>2]|0,h)|0;if((c[j>>2]|0)==0){if((c[h>>2]|0)==0){c[h>>2]=1472}c[d>>2]=c[h>>2];k=c[d>>2]|0;i=b;return k|0}c[f>>2]=Ob[c[(c[(c[e>>2]|0)+8>>2]|0)+116>>2]&7](c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[j>>2]|0)|0;if((c[f>>2]|0)==0){Ba(936,888,1402,1496)}Fd(c[e>>2]|0);Ld(c[e>>2]|0);if((c[(c[e>>2]|0)+52>>2]|0)>=(c[(c[e>>2]|0)+56>>2]|0)){c[(c[e>>2]|0)+56>>2]=(c[(c[e>>2]|0)+52>>2]|0)+128;h=ud(c[(c[e>>2]|0)+64>>2]|0,(c[(c[e>>2]|0)+56>>2]|0)*12|0)|0;c[(c[e>>2]|0)+64>>2]=h}c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+52>>2]|0)*12|0)>>2]=c[f>>2];c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+52>>2]|0)*12|0)+4>>2]=c[j>>2];c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+52>>2]|0)*12|0)+8>>2]=2;j=(c[e>>2]|0)+52|0;f=(c[j>>2]|0)+1|0;c[j>>2]=f;c[(c[e>>2]|0)+60>>2]=f;if((c[(c[e>>2]|0)+80>>2]|0)!=0){Lb[c[(c[(c[e>>2]|0)+8>>2]|0)+108>>2]&3](c[(c[e>>2]|0)+80>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-2|0)*12|0)>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0)}c[(c[e>>2]|0)+104>>2]=1;f=c[e>>2]|0;if((c[(c[(c[e>>2]|0)+8>>2]|0)+188>>2]&512|0)!=0){j=Jb[c[(c[f+8>>2]|0)+64>>2]&15](c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-2|0)*12|0)>>2]|0)|0;c[(c[e>>2]|0)+84>>2]=j;l=+Pb[c[(c[(c[e>>2]|0)+8>>2]|0)+148>>2]&3](c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-2|0)*12|0)>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,1,c[(c[e>>2]|0)+80>>2]|0);g[(c[e>>2]|0)+88>>2]=l;g[(c[e>>2]|0)+92>>2]=0.0}else{g[f+88>>2]=0.0;Jd(c[e>>2]|0)}if((c[(c[e>>2]|0)+120>>2]|0)!=0){Dd(c[e>>2]|0)}Gd(c[e>>2]|0);c[d>>2]=0;k=c[d>>2]|0;i=b;return k|0}function ae(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;d=i;i=i+144|0;e=d;f=d+28|0;h=d+24|0;j=d+20|0;k=d+32|0;l=d+16|0;m=d+12|0;n=d+8|0;c[h>>2]=a;c[j>>2]=b;if((c[(c[h>>2]|0)+116>>2]|0)!=(c[j>>2]|0)){td(c[(c[h>>2]|0)+116>>2]|0);b=vd(c[j>>2]|0)|0;c[(c[h>>2]|0)+116>>2]=b}if((c[(c[(c[h>>2]|0)+8>>2]|0)+180>>2]|0)!=0){c[n>>2]=~~+g[(c[h>>2]|0)+112>>2];c[m>>2]=(c[n>>2]|0)/60|0;c[n>>2]=(c[n>>2]|0)%60|0;h=c[n>>2]|0;c[e>>2]=c[m>>2];c[e+4>>2]=h;ab(k|0,1512,e|0)|0;e=bg(k|0)|0;c[l>>2]=sd(e+(bg(c[j>>2]|0)|0)+1|0)|0;gg(c[l>>2]|0,k|0)|0;dg(c[l>>2]|0,c[j>>2]|0)|0;c[f>>2]=c[l>>2];o=c[f>>2]|0;i=d;return o|0}else{c[f>>2]=vd(c[j>>2]|0)|0;o=c[f>>2]|0;i=d;return o|0}return 0}function be(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+4|0;e=b;c[e>>2]=a;if((c[(c[e>>2]|0)+60>>2]|0)<=1){c[d>>2]=0;f=c[d>>2]|0;i=b;return f|0}if((c[(c[e>>2]|0)+80>>2]|0)!=0){Lb[c[(c[(c[e>>2]|0)+8>>2]|0)+108>>2]&3](c[(c[e>>2]|0)+80>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-2|0)*12|0)>>2]|0)}a=(c[e>>2]|0)+60|0;c[a>>2]=(c[a>>2]|0)+ -1;c[(c[e>>2]|0)+104>>2]=-1;c[d>>2]=1;f=c[d>>2]|0;i=b;return f|0}function ce(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+4|0;e=b;c[e>>2]=a;if((c[(c[e>>2]|0)+60>>2]|0)>=(c[(c[e>>2]|0)+52>>2]|0)){c[d>>2]=0;f=c[d>>2]|0;i=b;return f|0}if((c[(c[e>>2]|0)+80>>2]|0)!=0){Lb[c[(c[(c[e>>2]|0)+8>>2]|0)+108>>2]&3](c[(c[e>>2]|0)+80>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+(((c[(c[e>>2]|0)+60>>2]|0)-1|0)*12|0)>>2]|0,c[(c[(c[e>>2]|0)+64>>2]|0)+((c[(c[e>>2]|0)+60>>2]|0)*12|0)>>2]|0)}a=(c[e>>2]|0)+60|0;c[a>>2]=(c[a>>2]|0)+1;c[(c[e>>2]|0)+104>>2]=1;c[d>>2]=1;f=c[d>>2]|0;i=b;return f|0}function de(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;c[e>>2]=c[d>>2];while(1){if((c[(c[e>>2]|0)+4>>2]|0)==3){break}if((c[(c[e>>2]|0)+4>>2]|0)==0){td(c[(c[e>>2]|0)+8>>2]|0)}c[e>>2]=(c[e>>2]|0)+16}td(c[d>>2]|0);i=b;return}function ee(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;f=i;i=i+32|0;g=f+24|0;h=f+20|0;j=f+16|0;k=f+12|0;l=f+8|0;m=f+4|0;n=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=c[g>>2];c[m>>2]=c[h>>2];while(1){h=c[m>>2]|0;c[m>>2]=h+ -1;if((h|0)<=1){break}c[n>>2]=qe(c[k>>2]|0,(c[m>>2]|0)+1|0)|0;if((c[n>>2]|0)==(c[m>>2]|0)){continue}h=(c[l>>2]|0)+(Z(c[j>>2]|0,c[m>>2]|0)|0)|0;g=(c[l>>2]|0)+(Z(c[j>>2]|0,c[n>>2]|0)|0)|0;fe(h,g,c[j>>2]|0)}i=f;return}function fe(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0;e=i;i=i+544|0;f=e+20|0;g=e+16|0;h=e+12|0;j=e+24|0;k=e+8|0;l=e+4|0;m=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;c[k>>2]=c[f>>2];c[l>>2]=c[g>>2];while(1){if((c[h>>2]|0)<=0){break}c[m>>2]=(c[h>>2]|0)>>>0<512?c[h>>2]|0:512;eg(j|0,c[k>>2]|0,c[m>>2]|0)|0;eg(c[k>>2]|0,c[l>>2]|0,c[m>>2]|0)|0;eg(c[l>>2]|0,j|0,c[m>>2]|0)|0;c[k>>2]=(c[k>>2]|0)+(c[m>>2]|0);c[l>>2]=(c[l>>2]|0)+(c[m>>2]|0);c[h>>2]=(c[h>>2]|0)-(c[m>>2]|0)}i=e;return}function ge(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;h=i;i=i+80|0;j=h+68|0;k=h+64|0;l=h+60|0;m=h+56|0;n=h+52|0;o=h+48|0;p=h+44|0;q=h+40|0;r=h+36|0;s=h+32|0;t=h;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=f;c[o>>2]=g;c[p>>2]=c[k>>2];c[q>>2]=(c[k>>2]|0)+(c[m>>2]|0)-1;c[r>>2]=c[l>>2];c[s>>2]=(c[l>>2]|0)+(c[n>>2]|0)-1;c[t>>2]=c[p>>2];c[t+4>>2]=c[r>>2];c[t+8>>2]=c[p>>2];c[t+12>>2]=c[s>>2];c[t+16>>2]=c[q>>2];c[t+20>>2]=c[s>>2];c[t+24>>2]=c[q>>2];c[t+28>>2]=c[r>>2];mc(c[j>>2]|0,t,4,-1,c[o>>2]|0);i=h;return}function he(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0;h=i;i=i+32|0;j=h+28|0;k=h+24|0;l=h+20|0;m=h+16|0;n=h+12|0;o=h+8|0;p=h+4|0;q=h;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=f;c[o>>2]=g;c[p>>2]=0;c[q>>2]=0;g=c[j>>2]|0;if((g|0)==521){c[q>>2]=-1}else if((g|0)==523){c[p>>2]=-1}else if((g|0)==522){c[q>>2]=1}else if((g|0)==524){c[p>>2]=1}else{i=h;return}g=(c[c[k>>2]>>2]|0)+(c[p>>2]|0)|0;if((c[o>>2]|0)!=0){c[c[k>>2]>>2]=(g+(c[m>>2]|0)|0)%(c[m>>2]|0)|0;c[c[l>>2]>>2]=((c[c[l>>2]>>2]|0)+(c[q>>2]|0)+(c[n>>2]|0)|0)%(c[n>>2]|0)|0;i=h;return}if((g|0)>0){r=(c[c[k>>2]>>2]|0)+(c[p>>2]|0)|0}else{r=0}if((r|0)<((c[m>>2]|0)-1|0)){if(((c[c[k>>2]>>2]|0)+(c[p>>2]|0)|0)>0){s=(c[c[k>>2]>>2]|0)+(c[p>>2]|0)|0}else{s=0}}else{s=(c[m>>2]|0)-1|0}c[c[k>>2]>>2]=s;if(((c[c[l>>2]>>2]|0)+(c[q>>2]|0)|0)>0){t=(c[c[l>>2]>>2]|0)+(c[q>>2]|0)|0}else{t=0}if((t|0)<((c[n>>2]|0)-1|0)){if(((c[c[l>>2]>>2]|0)+(c[q>>2]|0)|0)>0){u=(c[c[l>>2]>>2]|0)+(c[q>>2]|0)|0}else{u=0}}else{u=(c[n>>2]|0)-1|0}c[c[l>>2]>>2]=u;i=h;return}function ie(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;je(c[d>>2]|0);c[(c[d>>2]|0)+84>>2]=0;c[(c[d>>2]|0)+92>>2]=0;c[(c[d>>2]|0)+88>>2]=0;i=b;return}function je(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;c[c[d>>2]>>2]=1732584193;c[(c[d>>2]|0)+4>>2]=-271733879;c[(c[d>>2]|0)+8>>2]=-1732584194;c[(c[d>>2]|0)+12>>2]=271733878;c[(c[d>>2]|0)+16>>2]=-1009589776;i=b;return}function ke(a,b,e){a=a|0;b=b|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;f=i;i=i+96|0;g=f+84|0;h=f+80|0;j=f+76|0;k=f+72|0;l=f+8|0;m=f+4|0;n=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=e;c[k>>2]=c[h>>2];c[m>>2]=c[j>>2];h=(c[g>>2]|0)+92|0;c[h>>2]=(c[h>>2]|0)+(c[m>>2]|0);h=(c[g>>2]|0)+88|0;c[h>>2]=(c[h>>2]|0)+((c[(c[g>>2]|0)+92>>2]|0)>>>0<(c[m>>2]|0)>>>0);if((c[(c[g>>2]|0)+84>>2]|0)!=0?((c[(c[g>>2]|0)+84>>2]|0)+(c[j>>2]|0)|0)<64:0){eg((c[g>>2]|0)+20+(c[(c[g>>2]|0)+84>>2]|0)|0,c[k>>2]|0,c[j>>2]|0)|0;m=(c[g>>2]|0)+84|0;c[m>>2]=(c[m>>2]|0)+(c[j>>2]|0);i=f;return}while(1){o=(c[g>>2]|0)+20|0;if(((c[(c[g>>2]|0)+84>>2]|0)+(c[j>>2]|0)|0)<64){break}eg(o+(c[(c[g>>2]|0)+84>>2]|0)|0,c[k>>2]|0,64-(c[(c[g>>2]|0)+84>>2]|0)|0)|0;c[k>>2]=(c[k>>2]|0)+(64-(c[(c[g>>2]|0)+84>>2]|0));c[j>>2]=(c[j>>2]|0)-(64-(c[(c[g>>2]|0)+84>>2]|0));c[n>>2]=0;while(1){if((c[n>>2]|0)>=16){break}c[l+(c[n>>2]<<2)>>2]=(d[(c[g>>2]|0)+20+((c[n>>2]<<2)+0)|0]|0)<<24|(d[(c[g>>2]|0)+20+((c[n>>2]<<2)+1)|0]|0)<<16|(d[(c[g>>2]|0)+20+((c[n>>2]<<2)+2)|0]|0)<<8|(d[(c[g>>2]|0)+20+((c[n>>2]<<2)+3)|0]|0)<<0;c[n>>2]=(c[n>>2]|0)+1}le(c[g>>2]|0,l);c[(c[g>>2]|0)+84>>2]=0}eg(o|0,c[k>>2]|0,c[j>>2]|0)|0;c[(c[g>>2]|0)+84>>2]=c[j>>2];i=f;return}function le(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;d=i;i=i+384|0;e=d+372|0;f=d+368|0;g=d+48|0;h=d+40|0;j=d+36|0;k=d+32|0;l=d+28|0;m=d+24|0;n=d+20|0;o=d+16|0;p=d+12|0;q=d+8|0;r=d+4|0;s=d;c[e>>2]=a;c[f>>2]=b;c[n>>2]=0;while(1){if((c[n>>2]|0)>=16){break}c[g+(c[n>>2]<<2)>>2]=c[(c[f>>2]|0)+(c[n>>2]<<2)>>2];c[n>>2]=(c[n>>2]|0)+1}c[n>>2]=16;while(1){if((c[n>>2]|0)>=80){break}c[o>>2]=c[g+((c[n>>2]|0)-3<<2)>>2]^c[g+((c[n>>2]|0)-8<<2)>>2]^c[g+((c[n>>2]|0)-14<<2)>>2]^c[g+((c[n>>2]|0)-16<<2)>>2];c[g+(c[n>>2]<<2)>>2]=c[o>>2]<<1|(c[o>>2]|0)>>>31;c[n>>2]=(c[n>>2]|0)+1}c[h>>2]=c[c[e>>2]>>2];c[j>>2]=c[(c[e>>2]|0)+4>>2];c[k>>2]=c[(c[e>>2]|0)+8>>2];c[l>>2]=c[(c[e>>2]|0)+12>>2];c[m>>2]=c[(c[e>>2]|0)+16>>2];c[n>>2]=0;while(1){if((c[n>>2]|0)>=20){break}c[p>>2]=(c[h>>2]<<5|(c[h>>2]|0)>>>27)+(c[j>>2]&c[k>>2]|c[l>>2]&~c[j>>2])+(c[m>>2]|0)+(c[g+(c[n>>2]<<2)>>2]|0)+1518500249;c[m>>2]=c[l>>2];c[l>>2]=c[k>>2];c[k>>2]=c[j>>2]<<30|(c[j>>2]|0)>>>2;c[j>>2]=c[h>>2];c[h>>2]=c[p>>2];c[n>>2]=(c[n>>2]|0)+1}c[n>>2]=20;while(1){if((c[n>>2]|0)>=40){break}c[q>>2]=(c[h>>2]<<5|(c[h>>2]|0)>>>27)+(c[j>>2]^c[k>>2]^c[l>>2])+(c[m>>2]|0)+(c[g+(c[n>>2]<<2)>>2]|0)+1859775393;c[m>>2]=c[l>>2];c[l>>2]=c[k>>2];c[k>>2]=c[j>>2]<<30|(c[j>>2]|0)>>>2;c[j>>2]=c[h>>2];c[h>>2]=c[q>>2];c[n>>2]=(c[n>>2]|0)+1}c[n>>2]=40;while(1){if((c[n>>2]|0)>=60){break}c[r>>2]=(c[h>>2]<<5|(c[h>>2]|0)>>>27)+(c[j>>2]&c[k>>2]|c[j>>2]&c[l>>2]|c[k>>2]&c[l>>2])+(c[m>>2]|0)+(c[g+(c[n>>2]<<2)>>2]|0)+ -1894007588;c[m>>2]=c[l>>2];c[l>>2]=c[k>>2];c[k>>2]=c[j>>2]<<30|(c[j>>2]|0)>>>2;c[j>>2]=c[h>>2];c[h>>2]=c[r>>2];c[n>>2]=(c[n>>2]|0)+1}c[n>>2]=60;while(1){t=c[h>>2]|0;if((c[n>>2]|0)>=80){break}c[s>>2]=(t<<5|(c[h>>2]|0)>>>27)+(c[j>>2]^c[k>>2]^c[l>>2])+(c[m>>2]|0)+(c[g+(c[n>>2]<<2)>>2]|0)+ -899497514;c[m>>2]=c[l>>2];c[l>>2]=c[k>>2];c[k>>2]=c[j>>2]<<30|(c[j>>2]|0)>>>2;c[j>>2]=c[h>>2];c[h>>2]=c[s>>2];c[n>>2]=(c[n>>2]|0)+1}n=c[e>>2]|0;c[n>>2]=(c[n>>2]|0)+t;t=(c[e>>2]|0)+4|0;c[t>>2]=(c[t>>2]|0)+(c[j>>2]|0);j=(c[e>>2]|0)+8|0;c[j>>2]=(c[j>>2]|0)+(c[k>>2]|0);k=(c[e>>2]|0)+12|0;c[k>>2]=(c[k>>2]|0)+(c[l>>2]|0);l=(c[e>>2]|0)+16|0;c[l>>2]=(c[l>>2]|0)+(c[m>>2]|0);i=d;return}function me(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0;e=i;i=i+96|0;f=e+20|0;g=e+16|0;h=e+12|0;j=e+8|0;k=e+24|0;l=e+4|0;m=e;c[f>>2]=b;c[g>>2]=d;d=c[(c[f>>2]|0)+84>>2]|0;if((c[(c[f>>2]|0)+84>>2]|0)>=56){c[j>>2]=120-d}else{c[j>>2]=56-d}c[l>>2]=c[(c[f>>2]|0)+88>>2]<<3|(c[(c[f>>2]|0)+92>>2]|0)>>>29;c[m>>2]=c[(c[f>>2]|0)+92>>2]<<3;cg(k|0,0,c[j>>2]|0)|0;a[k]=-128;ke(c[f>>2]|0,k,c[j>>2]|0);a[k]=(c[l>>2]|0)>>>24&255;a[k+1|0]=(c[l>>2]|0)>>>16&255;a[k+2|0]=(c[l>>2]|0)>>>8&255;a[k+3|0]=(c[l>>2]|0)>>>0&255;a[k+4|0]=(c[m>>2]|0)>>>24&255;a[k+5|0]=(c[m>>2]|0)>>>16&255;a[k+6|0]=(c[m>>2]|0)>>>8&255;a[k+7|0]=(c[m>>2]|0)>>>0&255;ke(c[f>>2]|0,k,8);c[h>>2]=0;while(1){if((c[h>>2]|0)>=5){break}a[(c[g>>2]|0)+(c[h>>2]<<2)|0]=(c[(c[f>>2]|0)+(c[h>>2]<<2)>>2]|0)>>>24&255;a[(c[g>>2]|0)+((c[h>>2]<<2)+1)|0]=(c[(c[f>>2]|0)+(c[h>>2]<<2)>>2]|0)>>>16&255;a[(c[g>>2]|0)+((c[h>>2]<<2)+2)|0]=(c[(c[f>>2]|0)+(c[h>>2]<<2)>>2]|0)>>>8&255;a[(c[g>>2]|0)+((c[h>>2]<<2)+3)|0]=c[(c[f>>2]|0)+(c[h>>2]<<2)>>2]&255;c[h>>2]=(c[h>>2]|0)+1}i=e;return}function ne(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0;e=i;i=i+112|0;f=e+104|0;g=e+100|0;h=e+96|0;j=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;ie(j);ke(j,c[f>>2]|0,c[g>>2]|0);me(j,c[h>>2]|0);i=e;return}function oe(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;g=d;c[e>>2]=a;c[f>>2]=b;c[g>>2]=sd(64)|0;ne(c[e>>2]|0,c[f>>2]|0,c[g>>2]|0);ne(c[g>>2]|0,20,(c[g>>2]|0)+20|0);ne(c[g>>2]|0,40,(c[g>>2]|0)+40|0);c[(c[g>>2]|0)+60>>2]=0;i=d;return c[g>>2]|0}function pe(b,e){b=b|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;f=i;i=i+32|0;g=f+16|0;h=f+12|0;j=f+8|0;k=f+4|0;l=f;c[g>>2]=b;c[h>>2]=e;c[j>>2]=0;c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[h>>2]|0)){break}if((c[(c[g>>2]|0)+60>>2]|0)>=20){c[l>>2]=0;while(1){if((c[l>>2]|0)>=20){break}m=(c[g>>2]|0)+(c[l>>2]|0)|0;if((d[(c[g>>2]|0)+(c[l>>2]|0)|0]|0|0)!=255){n=7;break}a[m]=0;c[l>>2]=(c[l>>2]|0)+1}if((n|0)==7){n=0;a[m]=(a[m]|0)+1<<24>>24}ne(c[g>>2]|0,40,(c[g>>2]|0)+40|0);c[(c[g>>2]|0)+60>>2]=0}e=c[j>>2]<<8;b=(c[g>>2]|0)+60|0;o=c[b>>2]|0;c[b>>2]=o+1;c[j>>2]=e|(d[(c[g>>2]|0)+40+o|0]|0);c[k>>2]=(c[k>>2]|0)+8}c[j>>2]=c[j>>2]&(1<<(c[h>>2]|0)-1<<1)-1;i=f;return c[j>>2]|0}function qe(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0;d=i;i=i+32|0;e=d+20|0;f=d+16|0;g=d+12|0;h=d+8|0;j=d+4|0;k=d;c[e>>2]=a;c[f>>2]=b;c[g>>2]=0;while(1){l=c[g>>2]|0;if(((c[f>>2]|0)>>>(c[g>>2]|0)|0)==0){break}c[g>>2]=l+1}c[g>>2]=l+3;if((c[g>>2]|0)>=32){Ba(1592,1608,275,1624)}c[h>>2]=1<<c[g>>2];c[j>>2]=((c[h>>2]|0)>>>0)/((c[f>>2]|0)>>>0)|0;c[h>>2]=Z(c[f>>2]|0,c[j>>2]|0)|0;do{c[k>>2]=pe(c[e>>2]|0,c[g>>2]|0)|0}while((c[k>>2]|0)>>>0>=(c[h>>2]|0)>>>0);i=d;return((c[k>>2]|0)>>>0)/((c[j>>2]|0)>>>0)|0|0}function re(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;td(c[d>>2]|0);i=b;return}function se(){var a=0,b=0;a=i;i=i+16|0;b=a;c[b>>2]=sd(28)|0;c[(c[b>>2]|0)+4>>2]=3;c[c[b>>2]>>2]=3;c[(c[b>>2]|0)+20>>2]=0;c[(c[b>>2]|0)+24>>2]=0;c[(c[b>>2]|0)+8>>2]=1;c[(c[b>>2]|0)+12>>2]=0;c[(c[b>>2]|0)+16>>2]=3;i=a;return c[b>>2]|0}function te(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0;e=i;i=i+16|0;f=e+12|0;g=e+8|0;h=e+4|0;j=e;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;if((c[g>>2]|0)<0|(c[g>>2]|0)>>>0>=14){c[f>>2]=0;k=c[f>>2]|0;i=e;return k|0}else{d=vd(c[7752+(c[g>>2]<<5)>>2]|0)|0;c[c[h>>2]>>2]=d;d=xe(7756+(c[g>>2]<<5)|0)|0;c[c[j>>2]>>2]=d;c[f>>2]=1;k=c[f>>2]|0;i=e;return k|0}return 0}function ue(b,e){b=b|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;f=i;i=i+32|0;g=f+20|0;h=f+16|0;j=f+12|0;k=f+8|0;l=f+4|0;m=f;c[g>>2]=b;c[h>>2]=e;c[j>>2]=0;e=Zf(c[h>>2]|0)|0;c[(c[g>>2]|0)+4>>2]=e;c[c[g>>2]>>2]=e;c[(c[g>>2]|0)+20>>2]=0;c[(c[g>>2]|0)+24>>2]=0;while(1){if((a[c[h>>2]|0]|0)!=0){n=(rb(d[c[h>>2]|0]|0)|0)!=0}else{n=0}o=c[h>>2]|0;if(!n){break}c[h>>2]=o+1}a:do{if((a[o]|0)==120){c[h>>2]=(c[h>>2]|0)+1;n=Zf(c[h>>2]|0)|0;c[(c[g>>2]|0)+4>>2]=n;c[j>>2]=1;while(1){if((a[c[h>>2]|0]|0)==0){break a}if((rb(d[c[h>>2]|0]|0)|0)==0){break a}c[h>>2]=(c[h>>2]|0)+1}}}while(0);while(1){if((a[c[h>>2]|0]|0)==0){break}o=c[h>>2]|0;if((a[c[h>>2]|0]|0)==106){c[h>>2]=o+1;if((c[j>>2]|0)!=0){n=c[g>>2]|0;c[n>>2]=Z(c[n>>2]|0,c[(c[g>>2]|0)+4>>2]|0)|0}c[(c[g>>2]|0)+4>>2]=1;continue}n=c[h>>2]|0;if((a[o]|0)==120){c[h>>2]=n+1;c[(c[g>>2]|0)+20>>2]=1;continue}o=c[h>>2]|0;if((a[n]|0)==107){c[h>>2]=o+1;c[(c[g>>2]|0)+24>>2]=1;continue}if(((a[o]|0)!=114?(a[c[h>>2]|0]|0)!=109:0)?(a[c[h>>2]|0]|0)!=97:0){o=(a[c[h>>2]|0]|0)==100;c[h>>2]=(c[h>>2]|0)+1;if(!o){continue}o=c[h>>2]|0;if((a[c[h>>2]|0]|0)==116){c[h>>2]=o+1;c[(c[g>>2]|0)+12>>2]=0;continue}n=c[h>>2]|0;if((a[o]|0)==98){c[h>>2]=n+1;c[(c[g>>2]|0)+12>>2]=1;continue}o=c[h>>2]|0;if((a[n]|0)==105){c[h>>2]=o+1;c[(c[g>>2]|0)+12>>2]=2;continue}n=c[h>>2]|0;if((a[o]|0)==97){c[h>>2]=n+1;c[(c[g>>2]|0)+12>>2]=3;continue}o=c[h>>2]|0;if((a[n]|0)==101){c[h>>2]=o+1;c[(c[g>>2]|0)+12>>2]=4;continue}if((a[o]|0)!=117){continue}c[h>>2]=(c[h>>2]|0)+1;c[(c[g>>2]|0)+12>>2]=5;continue}o=c[h>>2]|0;c[h>>2]=o+1;c[l>>2]=a[o]|0;if((c[l>>2]|0)==109?(a[c[h>>2]|0]|0)==100:0){c[m>>2]=1;c[h>>2]=(c[h>>2]|0)+1}else{c[m>>2]=0}c[k>>2]=Zf(c[h>>2]|0)|0;while(1){if((a[c[h>>2]|0]|0)==0){break}if((rb(d[c[h>>2]|0]|0)|0)==0){break}c[h>>2]=(c[h>>2]|0)+1}if((c[l>>2]|0)==109?(c[k>>2]|0)==8:0){c[(c[g>>2]|0)+8>>2]=7}if((c[l>>2]|0)==109?(c[k>>2]|0)==4:0){c[(c[g>>2]|0)+8>>2]=(c[m>>2]|0)!=0?6:5}if((c[l>>2]|0)==109?(c[k>>2]|0)==2:0){c[(c[g>>2]|0)+8>>2]=(c[m>>2]|0)!=0?4:3}if((c[l>>2]|0)==114?(c[k>>2]|0)==4:0){c[(c[g>>2]|0)+8>>2]=2}if((c[l>>2]|0)==114?(c[k>>2]|0)==2:0){c[(c[g>>2]|0)+8>>2]=1}if((c[l>>2]|0)!=97){continue}c[(c[g>>2]|0)+8>>2]=0}i=f;return}function ve(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0;d=i;i=i+96|0;e=d;f=d+12|0;g=d+8|0;h=d+16|0;c[f>>2]=a;c[g>>2]=b;b=c[c[f>>2]>>2]|0;if((c[(c[f>>2]|0)+4>>2]|0)>1){a=c[(c[f>>2]|0)+4>>2]|0;c[e>>2]=b;c[e+4>>2]=a;ab(h|0,7624,e|0)|0}else{c[e>>2]=b;ab(h|0,7632,e|0)|0}if((c[(c[f>>2]|0)+20>>2]|0)!=0){dg(h|0,7640)|0}if((c[(c[f>>2]|0)+24>>2]|0)!=0){dg(h|0,7648)|0}a:do{if((c[g>>2]|0)!=0){switch(c[(c[f>>2]|0)+8>>2]|0){case 7:{dg(h|0,7656)|0;break};case 3:{dg(h|0,7680)|0;break};case 4:{dg(h|0,7688)|0;break};case 5:{dg(h|0,7664)|0;break};case 2:{dg(h|0,7696)|0;break};case 0:{dg(h|0,7704)|0;break};case 6:{dg(h|0,7672)|0;break};default:{}}switch(c[(c[f>>2]|0)+12>>2]|0){case 2:{dg(h|0,7720)|0;break a;break};case 3:{dg(h|0,7728)|0;break a;break};case 1:{dg(h|0,7712)|0;break a;break};case 4:{dg(h|0,7736)|0;break a;break};case 5:{dg(h|0,7744)|0;break a;break};default:{break a}}}}while(0);f=vd(h)|0;i=d;return f|0}function we(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;td(c[d>>2]|0);i=b;return}function xe(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;c[e>>2]=sd(28)|0;a=c[e>>2]|0;f=c[d>>2]|0;c[a+0>>2]=c[f+0>>2];c[a+4>>2]=c[f+4>>2];c[a+8>>2]=c[f+8>>2];c[a+12>>2]=c[f+12>>2];c[a+16>>2]=c[f+16>>2];c[a+20>>2]=c[f+20>>2];c[a+24>>2]=c[f+24>>2];i=b;return c[e>>2]|0}function ye(a){a=a|0;var b=0,d=0,e=0,f=0,g=0;b=i;i=i+96|0;d=b;e=b+8|0;f=b+4|0;g=b+16|0;c[e>>2]=a;c[f>>2]=sd(128)|0;c[c[f>>2]>>2]=7240;c[(c[f>>2]|0)+4>>2]=0;c[d>>2]=c[c[e>>2]>>2];ab(g|0,4512,d|0)|0;a=vd(g)|0;c[(c[f>>2]|0)+8>>2]=a;c[(c[f>>2]|0)+12>>2]=0;c[(c[f>>2]|0)+16>>2]=7264;c[(c[f>>2]|0)+20>>2]=0;c[d>>2]=c[(c[e>>2]|0)+4>>2];ab(g|0,4512,d|0)|0;d=vd(g)|0;c[(c[f>>2]|0)+24>>2]=d;c[(c[f>>2]|0)+28>>2]=0;c[(c[f>>2]|0)+32>>2]=7288;c[(c[f>>2]|0)+36>>2]=2;c[(c[f>>2]|0)+40>>2]=0;c[(c[f>>2]|0)+44>>2]=c[(c[e>>2]|0)+20>>2];c[(c[f>>2]|0)+48>>2]=7344;c[(c[f>>2]|0)+52>>2]=2;c[(c[f>>2]|0)+56>>2]=0;c[(c[f>>2]|0)+60>>2]=(c[(c[e>>2]|0)+4>>2]|0)==1;c[(c[f>>2]|0)+64>>2]=7384;c[(c[f>>2]|0)+68>>2]=2;c[(c[f>>2]|0)+72>>2]=0;c[(c[f>>2]|0)+76>>2]=c[(c[e>>2]|0)+24>>2];c[(c[f>>2]|0)+80>>2]=7408;c[(c[f>>2]|0)+84>>2]=1;c[(c[f>>2]|0)+88>>2]=7424;c[(c[f>>2]|0)+92>>2]=c[(c[e>>2]|0)+8>>2];c[(c[f>>2]|0)+96>>2]=7544;c[(c[f>>2]|0)+100>>2]=1;c[(c[f>>2]|0)+104>>2]=7560;c[(c[f>>2]|0)+108>>2]=c[(c[e>>2]|0)+12>>2];c[(c[f>>2]|0)+112>>2]=0;c[(c[f>>2]|0)+116>>2]=3;c[(c[f>>2]|0)+120>>2]=0;c[(c[f>>2]|0)+124>>2]=0;i=b;return c[f>>2]|0}function ze(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[d>>2]=a;c[e>>2]=sd(28)|0;a=Zf(c[(c[d>>2]|0)+8>>2]|0)|0;c[c[e>>2]>>2]=a;a=Zf(c[(c[d>>2]|0)+24>>2]|0)|0;c[(c[e>>2]|0)+4>>2]=a;c[(c[e>>2]|0)+20>>2]=c[(c[d>>2]|0)+44>>2];if((c[(c[d>>2]|0)+60>>2]|0)!=0){a=c[e>>2]|0;c[a>>2]=Z(c[a>>2]|0,c[(c[e>>2]|0)+4>>2]|0)|0;c[(c[e>>2]|0)+4>>2]=1}c[(c[e>>2]|0)+24>>2]=c[(c[d>>2]|0)+76>>2];c[(c[e>>2]|0)+8>>2]=c[(c[d>>2]|0)+92>>2];c[(c[e>>2]|0)+12>>2]=c[(c[d>>2]|0)+108>>2];c[(c[e>>2]|0)+16>>2]=3;i=b;return c[e>>2]|0}function Ae(a,b){a=a|0;b=b|0;var d=0,e=0,f=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;c[f>>2]=a;c[d>>2]=b;do{if((c[c[f>>2]>>2]|0)<2){c[e>>2]=7032}else{if((c[c[f>>2]>>2]|0)<=255?(c[(c[f>>2]|0)+4>>2]|0)<=255:0){if((Z(c[c[f>>2]>>2]|0,c[(c[f>>2]|0)+4>>2]|0)|0)>31){c[e>>2]=7120;break}if((c[(c[f>>2]|0)+24>>2]|0)!=0?(Z(c[c[f>>2]>>2]|0,c[(c[f>>2]|0)+4>>2]|0)|0)>9:0){c[e>>2]=7184;break}c[e>>2]=0;break}c[e>>2]=7072}}while(0);i=d;return c[e>>2]|0}function Be(b,d,e,f){b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0,L=0,M=0,N=0,O=0;g=i;i=i+192|0;h=g+188|0;j=g+184|0;k=g+180|0;l=g+172|0;m=g+168|0;n=g+164|0;o=g+160|0;p=g+156|0;q=g+152|0;r=g+148|0;s=g+144|0;t=g+140|0;u=g+136|0;v=g+132|0;w=g+128|0;x=g+64|0;y=g+56|0;z=g+52|0;A=g+48|0;B=g+44|0;C=g+40|0;D=g+24|0;E=g+20|0;F=g+16|0;G=g+12|0;H=g+8|0;I=g+4|0;J=g;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[g+176>>2]=f;c[l>>2]=c[c[h>>2]>>2];c[m>>2]=c[(c[h>>2]|0)+4>>2];c[n>>2]=Z(c[l>>2]|0,c[m>>2]|0)|0;c[o>>2]=Z(c[n>>2]|0,c[n>>2]|0)|0;wf();c[D>>2]=c[(c[h>>2]|0)+12>>2];c[D+4>>2]=c[(c[h>>2]|0)+16>>2];if((c[l>>2]|0)==2?(c[m>>2]|0)==2:0){c[D>>2]=0}c[r>>2]=sd(c[o>>2]|0)|0;c[u>>2]=sd(c[o>>2]<<3)|0;c[s>>2]=sd(c[o>>2]|0)|0;c[p>>2]=hf(c[l>>2]|0,c[m>>2]|0,c[o>>2]|0,c[n>>2]|0,c[n>>2]|0)|0;c[q>>2]=0;if((c[(c[h>>2]|0)+24>>2]|0)!=0){K=sd(c[o>>2]|0)|0}else{K=0}c[t>>2]=K;while(1){a:do{if((c[m>>2]|0)==1){c[E>>2]=fc(c[n>>2]|0,c[n>>2]|0,c[n>>2]|0,c[j>>2]|0)|0;zf(c[E>>2]|0,c[p>>2]|0,c[n>>2]|0,c[n>>2]|0);td(c[E>>2]|0)}else{c[A>>2]=0;while(1){if((c[A>>2]|0)>=(c[n>>2]|0)){break a}c[z>>2]=0;while(1){L=c[A>>2]|0;if((c[z>>2]|0)>=(c[n>>2]|0)){break}K=Z((L|0)/(c[l>>2]|0)|0,c[l>>2]|0)|0;f=Z(c[A>>2]|0,c[n>>2]|0)|0;c[(c[(c[p>>2]|0)+16>>2]|0)+(f+(c[z>>2]|0)<<2)>>2]=K+((c[z>>2]|0)/(c[m>>2]|0)|0);c[z>>2]=(c[z>>2]|0)+1}c[A>>2]=L+1}}}while(0);Af(c[p>>2]|0);if((c[(c[h>>2]|0)+24>>2]|0)!=0){if((c[q>>2]|0)!=0){uf(c[q>>2]|0)}c[q>>2]=Ef(c[n>>2]|0,c[j>>2]|0,(c[(c[h>>2]|0)+16>>2]|0)>0|0)|0}if((Ff(c[n>>2]|0,c[p>>2]|0,c[q>>2]|0,c[(c[h>>2]|0)+20>>2]|0,c[r>>2]|0,c[j>>2]|0,Z(c[o>>2]|0,c[o>>2]|0)|0)|0)==0){continue}if((cf(c[n>>2]|0,c[p>>2]|0,c[q>>2]|0,c[(c[h>>2]|0)+20>>2]|0,c[r>>2]|0)|0)==0){M=21;break}if((c[c[k>>2]>>2]|0)!=0){td(c[c[k>>2]>>2]|0)}K=ff(c[n>>2]|0,c[r>>2]|0)|0;c[c[k>>2]>>2]=K;if((c[(c[h>>2]|0)+24>>2]|0)!=0){c[F>>2]=0;c[G>>2]=0;c[H>>2]=0;eg(c[s>>2]|0,c[r>>2]|0,c[o>>2]|0)|0;while(1){Gf(c[q>>2]|0,c[t>>2]|0,c[s>>2]|0,c[o>>2]|0);cg(c[r>>2]|0,0,c[o>>2]|0)|0;ef(c[n>>2]|0,c[p>>2]|0,c[q>>2]|0,c[(c[h>>2]|0)+20>>2]|0,c[r>>2]|0,c[t>>2]|0,D);if((c[D+8>>2]|0)==(c[D>>2]|0)?(c[D+12>>2]|0)==(c[D+4>>2]|0):0){if((c[F>>2]|0)!=0){uf(c[F>>2]|0)}c[H>>2]=0;c[F>>2]=gf(c[q>>2]|0)|0;if((Hf(c[q>>2]|0,c[n>>2]|0,c[o>>2]|0,c[s>>2]|0,c[j>>2]|0)|0)!=0){continue}else{break}}if((c[D+8>>2]|0)<=(c[D>>2]|0)?(c[D+12>>2]|0)<=(c[D+4>>2]|0):0){if((c[G>>2]|0)!=0){uf(c[G>>2]|0)}c[G>>2]=gf(c[q>>2]|0)|0;if((Hf(c[q>>2]|0,c[n>>2]|0,c[o>>2]|0,c[s>>2]|0,c[j>>2]|0)|0)!=0){continue}else{break}}K=(c[H>>2]|0)+1|0;c[H>>2]=K;if((K|0)>50){break}if((c[F>>2]|0)!=0){uf(c[q>>2]|0);c[q>>2]=gf(c[F>>2]|0)|0;if((Hf(c[q>>2]|0,c[n>>2]|0,c[o>>2]|0,c[s>>2]|0,c[j>>2]|0)|0)!=0){continue}else{break}}if((c[G>>2]|0)==0){break}uf(c[q>>2]|0);c[q>>2]=c[G>>2];c[G>>2]=0}if((c[G>>2]|0)!=0){uf(c[G>>2]|0)}if((c[F>>2]|0)!=0){M=44;break}else{continue}}c[v>>2]=0;c[A>>2]=0;while(1){if((c[A>>2]|0)>=(c[n>>2]|0)){break}c[z>>2]=0;while(1){N=c[A>>2]|0;if((c[z>>2]|0)>=(c[n>>2]|0)){break}K=Z(N,c[n>>2]|0)|0;c[I>>2]=K+(c[z>>2]|0);c[y>>2]=If(c[h>>2]|0,c[z>>2]|0,c[A>>2]|0,x,c[(c[h>>2]|0)+8>>2]|0)|0;c[J>>2]=0;while(1){if((c[J>>2]|0)>=(c[y>>2]|0)){break}K=Z(c[x+((c[J>>2]<<1)+1<<2)>>2]|0,c[n>>2]|0)|0;if((K+(c[x+(c[J>>2]<<1<<2)>>2]|0)|0)<(c[I>>2]|0)){break}c[J>>2]=(c[J>>2]|0)+1}if((c[J>>2]|0)==(c[y>>2]|0)){c[(c[u>>2]|0)+(c[v>>2]<<3)>>2]=c[z>>2];c[(c[u>>2]|0)+(c[v>>2]<<3)+4>>2]=c[A>>2];c[v>>2]=(c[v>>2]|0)+1}c[z>>2]=(c[z>>2]|0)+1}c[A>>2]=N+1}ee(c[u>>2]|0,c[v>>2]|0,8,c[j>>2]|0);c[B>>2]=0;while(1){if((c[B>>2]|0)>=(c[v>>2]|0)){break}c[z>>2]=c[(c[u>>2]|0)+(c[B>>2]<<3)>>2];c[A>>2]=c[(c[u>>2]|0)+(c[B>>2]<<3)+4>>2];eg(c[s>>2]|0,c[r>>2]|0,c[o>>2]|0)|0;c[y>>2]=If(c[h>>2]|0,c[z>>2]|0,c[A>>2]|0,x,c[(c[h>>2]|0)+8>>2]|0)|0;c[C>>2]=0;while(1){if((c[C>>2]|0)>=(c[y>>2]|0)){break}K=Z(c[x+((c[C>>2]<<1)+1<<2)>>2]|0,c[n>>2]|0)|0;a[(c[s>>2]|0)+(K+(c[x+(c[C>>2]<<1<<2)>>2]|0))|0]=0;c[C>>2]=(c[C>>2]|0)+1}ef(c[n>>2]|0,c[p>>2]|0,c[q>>2]|0,c[(c[h>>2]|0)+20>>2]|0,c[s>>2]|0,c[t>>2]|0,D);b:do{if((c[D+8>>2]|0)<=(c[D>>2]|0)){if((c[(c[h>>2]|0)+24>>2]|0)!=0?(c[D+12>>2]|0)>(c[D+4>>2]|0):0){break}c[C>>2]=0;while(1){if((c[C>>2]|0)>=(c[y>>2]|0)){break b}K=Z(c[x+((c[C>>2]<<1)+1<<2)>>2]|0,c[n>>2]|0)|0;a[(c[r>>2]|0)+(K+(c[x+(c[C>>2]<<1<<2)>>2]|0))|0]=0;c[C>>2]=(c[C>>2]|0)+1}}}while(0);c[B>>2]=(c[B>>2]|0)+1}eg(c[s>>2]|0,c[r>>2]|0,c[o>>2]|0)|0;ef(c[n>>2]|0,c[p>>2]|0,c[q>>2]|0,c[(c[h>>2]|0)+20>>2]|0,c[s>>2]|0,c[t>>2]|0,D);if((c[D+8>>2]|0)!=(c[D>>2]|0)){continue}if((c[(c[h>>2]|0)+24>>2]|0)==0){break}if((c[D+12>>2]|0)==(c[D+4>>2]|0)){break}}if((M|0)==21){Ba(6808,4528,3622,6864)}else if((M|0)==44){uf(c[q>>2]|0);c[q>>2]=c[F>>2];Gf(c[q>>2]|0,c[t>>2]|0,c[s>>2]|0,c[o>>2]|0);cg(c[r>>2]|0,0,c[o>>2]|0)|0}td(c[s>>2]|0);td(c[u>>2]|0);c[w>>2]=Jf(c[h>>2]|0,c[r>>2]|0,c[p>>2]|0,c[t>>2]|0,c[q>>2]|0)|0;td(c[r>>2]|0);uf(c[p>>2]|0);if((c[(c[h>>2]|0)+24>>2]|0)==0){O=c[w>>2]|0;i=g;return O|0}uf(c[q>>2]|0);td(c[t>>2]|0);O=c[w>>2]|0;i=g;return O|0}function Ce(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0;e=i;i=i+32|0;f=e+20|0;g=e+16|0;h=e+12|0;j=e+8|0;k=e+4|0;l=e;c[g>>2]=b;c[h>>2]=d;c[j>>2]=Z(c[c[g>>2]>>2]|0,c[(c[g>>2]|0)+4>>2]|0)|0;c[k>>2]=Z(c[j>>2]|0,c[j>>2]|0)|0;c[l>>2]=Cf(h,c[j>>2]|0,c[k>>2]|0)|0;if((c[l>>2]|0)!=0){c[f>>2]=c[l>>2];m=c[f>>2]|0;i=e;return m|0}if((c[(c[g>>2]|0)+4>>2]|0)==1){if((a[c[h>>2]|0]|0)!=44){c[f>>2]=6264;m=c[f>>2]|0;i=e;return m|0}c[h>>2]=(c[h>>2]|0)+1;c[l>>2]=Df(h,c[j>>2]|0,c[k>>2]|0,c[j>>2]|0,c[j>>2]|0,c[j>>2]|0,c[j>>2]|0)|0;if((c[l>>2]|0)!=0){c[f>>2]=c[l>>2];m=c[f>>2]|0;i=e;return m|0}}if((c[(c[g>>2]|0)+24>>2]|0)!=0){if((a[c[h>>2]|0]|0)!=44){c[f>>2]=6320;m=c[f>>2]|0;i=e;return m|0}c[h>>2]=(c[h>>2]|0)+1;c[l>>2]=Df(h,c[j>>2]|0,c[k>>2]|0,c[j>>2]|0,c[k>>2]|0,2,c[j>>2]|0)|0;if((c[l>>2]|0)!=0){c[f>>2]=c[l>>2];m=c[f>>2]|0;i=e;return m|0}if((a[c[h>>2]|0]|0)!=44){c[f>>2]=6376;m=c[f>>2]|0;i=e;return m|0}c[h>>2]=(c[h>>2]|0)+1;g=Z(c[j>>2]|0,c[k>>2]|0)|0;c[l>>2]=Cf(h,g,c[k>>2]|0)|0;if((c[l>>2]|0)!=0){c[f>>2]=c[l>>2];m=c[f>>2]|0;i=e;return m|0}}if((a[c[h>>2]|0]|0)!=0){c[f>>2]=6424;m=c[f>>2]|0;i=e;return m|0}else{c[f>>2]=0;m=c[f>>2]|0;i=e;return m|0}return 0}function De(b,e,f){b=b|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0;g=i;i=i+64|0;h=g+52|0;j=g+48|0;k=g+44|0;l=g+40|0;m=g+36|0;n=g+32|0;o=g+28|0;p=g+24|0;q=g+20|0;r=g+16|0;s=g+12|0;t=g+8|0;u=g+4|0;v=g;c[g+56>>2]=b;c[h>>2]=e;c[j>>2]=f;c[k>>2]=sd(44)|0;c[l>>2]=c[c[h>>2]>>2];c[m>>2]=c[(c[h>>2]|0)+4>>2];c[n>>2]=Z(c[l>>2]|0,c[m>>2]|0)|0;c[o>>2]=Z(c[n>>2]|0,c[n>>2]|0)|0;wf();c[c[k>>2]>>2]=c[n>>2];c[(c[k>>2]|0)+12>>2]=c[(c[h>>2]|0)+20>>2];c[(c[k>>2]|0)+16>>2]=c[(c[h>>2]|0)+24>>2];f=sd(c[o>>2]|0)|0;c[(c[k>>2]|0)+20>>2]=f;f=sd(Z(c[o>>2]|0,c[n>>2]|0)|0)|0;c[(c[k>>2]|0)+28>>2]=f;cg(c[(c[k>>2]|0)+28>>2]|0,0,Z(c[o>>2]|0,c[n>>2]|0)|0)|0;f=sd(c[o>>2]|0)|0;c[(c[k>>2]|0)+32>>2]=f;cg(c[(c[k>>2]|0)+32>>2]|0,0,c[o>>2]|0)|0;f=hf(c[l>>2]|0,c[m>>2]|0,c[o>>2]|0,c[n>>2]|0,c[n>>2]|0)|0;c[(c[k>>2]|0)+4>>2]=f;if((c[(c[h>>2]|0)+24>>2]|0)!=0){f=hf(c[l>>2]|0,c[m>>2]|0,c[o>>2]|0,c[n>>2]|0,c[o>>2]|0)|0;c[(c[k>>2]|0)+8>>2]=f;f=sd(c[o>>2]|0)|0;c[(c[k>>2]|0)+24>>2]=f}else{c[(c[k>>2]|0)+8>>2]=0;c[(c[k>>2]|0)+24>>2]=0}c[(c[k>>2]|0)+40>>2]=0;c[(c[k>>2]|0)+36>>2]=0;c[j>>2]=xf(c[j>>2]|0,c[(c[k>>2]|0)+20>>2]|0,c[o>>2]|0)|0;c[p>>2]=0;while(1){if((c[p>>2]|0)>=(c[o>>2]|0)){break}if((d[(c[(c[k>>2]|0)+20>>2]|0)+(c[p>>2]|0)|0]|0)!=0){a[(c[(c[k>>2]|0)+32>>2]|0)+(c[p>>2]|0)|0]=1}c[p>>2]=(c[p>>2]|0)+1}a:do{if((c[m>>2]|0)==1){if((a[c[j>>2]|0]|0)!=44){Ba(5704,4528,4079,5720)}c[j>>2]=(c[j>>2]|0)+1;c[q>>2]=yf(j,r,c[n>>2]|0,c[o>>2]|0)|0;if((c[q>>2]|0)==0){zf(c[r>>2]|0,c[(c[k>>2]|0)+4>>2]|0,c[n>>2]|0,c[n>>2]|0);td(c[r>>2]|0);break}else{Ba(5736,4528,4082,5720)}}else{c[t>>2]=0;while(1){if((c[t>>2]|0)>=(c[n>>2]|0)){break a}c[s>>2]=0;while(1){w=c[t>>2]|0;if((c[s>>2]|0)>=(c[n>>2]|0)){break}p=Z((w|0)/(c[l>>2]|0)|0,c[l>>2]|0)|0;f=Z(c[t>>2]|0,c[n>>2]|0)|0;c[(c[(c[(c[k>>2]|0)+4>>2]|0)+16>>2]|0)+(f+(c[s>>2]|0)<<2)>>2]=p+((c[s>>2]|0)/(c[m>>2]|0)|0);c[s>>2]=(c[s>>2]|0)+1}c[t>>2]=w+1}}}while(0);Af(c[(c[k>>2]|0)+4>>2]|0);do{if((c[(c[h>>2]|0)+24>>2]|0)!=0){if((a[c[j>>2]|0]|0)!=44){Ba(5704,4528,4097,5720)}c[j>>2]=(c[j>>2]|0)+1;c[u>>2]=yf(j,v,c[n>>2]|0,c[o>>2]|0)|0;if((c[u>>2]|0)!=0){Ba(5736,4528,4100,5720)}zf(c[v>>2]|0,c[(c[k>>2]|0)+8>>2]|0,c[n>>2]|0,c[o>>2]|0);td(c[v>>2]|0);Af(c[(c[k>>2]|0)+8>>2]|0);if((a[c[j>>2]|0]|0)==44){c[j>>2]=(c[j>>2]|0)+1;c[j>>2]=xf(c[j>>2]|0,c[(c[k>>2]|0)+24>>2]|0,c[o>>2]|0)|0;break}else{Ba(5704,4528,4105,5720)}}}while(0);if((a[c[j>>2]|0]|0)!=0){Ba(5752,4528,4109,5720)}else{i=g;return c[k>>2]|0}return 0}function Ee(a){a=a|0;var b=0,d=0,e=0,f=0,g=0;b=i;i=i+16|0;d=b+12|0;e=b+8|0;f=b+4|0;g=b;c[d>>2]=a;c[e>>2]=sd(44)|0;c[f>>2]=c[c[d>>2]>>2];c[g>>2]=Z(c[f>>2]|0,c[f>>2]|0)|0;c[c[e>>2]>>2]=c[c[d>>2]>>2];c[(c[e>>2]|0)+12>>2]=c[(c[d>>2]|0)+12>>2];c[(c[e>>2]|0)+16>>2]=c[(c[d>>2]|0)+16>>2];c[(c[e>>2]|0)+4>>2]=c[(c[d>>2]|0)+4>>2];a=c[(c[e>>2]|0)+4>>2]|0;c[a>>2]=(c[a>>2]|0)+1;c[(c[e>>2]|0)+8>>2]=c[(c[d>>2]|0)+8>>2];if((c[(c[e>>2]|0)+8>>2]|0)!=0){a=c[(c[e>>2]|0)+8>>2]|0;c[a>>2]=(c[a>>2]|0)+1}a=sd(c[g>>2]|0)|0;c[(c[e>>2]|0)+20>>2]=a;eg(c[(c[e>>2]|0)+20>>2]|0,c[(c[d>>2]|0)+20>>2]|0,c[g>>2]|0)|0;if((c[(c[d>>2]|0)+16>>2]|0)!=0){a=sd(c[g>>2]|0)|0;c[(c[e>>2]|0)+24>>2]=a;eg(c[(c[e>>2]|0)+24>>2]|0,c[(c[d>>2]|0)+24>>2]|0,c[g>>2]|0)|0}else{c[(c[e>>2]|0)+24>>2]=0}a=sd(Z(c[g>>2]|0,c[f>>2]|0)|0)|0;c[(c[e>>2]|0)+28>>2]=a;eg(c[(c[e>>2]|0)+28>>2]|0,c[(c[d>>2]|0)+28>>2]|0,Z(c[g>>2]|0,c[f>>2]|0)|0)|0;f=sd(c[g>>2]|0)|0;c[(c[e>>2]|0)+32>>2]=f;eg(c[(c[e>>2]|0)+32>>2]|0,c[(c[d>>2]|0)+32>>2]|0,c[g>>2]|0)|0;c[(c[e>>2]|0)+36>>2]=c[(c[d>>2]|0)+36>>2];c[(c[e>>2]|0)+40>>2]=c[(c[d>>2]|0)+40>>2];i=b;return c[e>>2]|0}function Fe(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b;c[d>>2]=a;uf(c[(c[d>>2]|0)+4>>2]|0);if((c[(c[d>>2]|0)+8>>2]|0)!=0){uf(c[(c[d>>2]|0)+8>>2]|0)}td(c[(c[d>>2]|0)+32>>2]|0);td(c[(c[d>>2]|0)+28>>2]|0);td(c[(c[d>>2]|0)+20>>2]|0);if((c[(c[d>>2]|0)+24>>2]|0)==0){e=c[d>>2]|0;td(e);i=b;return}td(c[(c[d>>2]|0)+24>>2]|0);e=c[d>>2]|0;td(e);i=b;return}function Ge(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0;f=i;i=i+48|0;g=f+44|0;h=f+40|0;j=f+32|0;k=f+28|0;l=f+24|0;m=f+20|0;n=f+16|0;o=f;c[h>>2]=a;c[f+36>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=c[c[h>>2]>>2];if((c[j>>2]|0)!=0){c[g>>2]=vd(c[j>>2]|0)|0;p=c[g>>2]|0;i=f;return p|0}c[n>>2]=sd(Z(c[l>>2]|0,c[l>>2]|0)|0)|0;eg(c[n>>2]|0,c[(c[h>>2]|0)+20>>2]|0,Z(c[l>>2]|0,c[l>>2]|0)|0)|0;c[o>>2]=5;c[o+4>>2]=3;ef(c[l>>2]|0,c[(c[h>>2]|0)+4>>2]|0,c[(c[h>>2]|0)+8>>2]|0,c[(c[h>>2]|0)+12>>2]|0,c[n>>2]|0,c[(c[h>>2]|0)+24>>2]|0,o);c[c[k>>2]>>2]=0;if((c[o+8>>2]|0)!=7){if((c[o+8>>2]|0)==6){c[c[k>>2]>>2]=5008}}else{c[c[k>>2]>>2]=4968}if((c[c[k>>2]>>2]|0)!=0){td(c[n>>2]|0);c[g>>2]=0;p=c[g>>2]|0;i=f;return p|0}else{c[m>>2]=ff(c[l>>2]|0,c[n>>2]|0)|0;td(c[n>>2]|0);c[g>>2]=c[m>>2];p=c[g>>2]|0;i=f;return p|0}return 0}function He(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b+4|0;e=b;c[e>>2]=a;if((c[(c[e>>2]|0)+24>>2]|0)!=0){c[d>>2]=0}else{c[d>>2]=1}i=b;return c[d>>2]|0}function Ie(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;if((c[(c[d>>2]|0)+8>>2]|0)!=0){Ba(4880,4528,4437,4896)}else{a=df(c[c[d>>2]>>2]|0,c[(c[d>>2]|0)+4>>2]|0,c[(c[d>>2]|0)+12>>2]|0,c[(c[d>>2]|0)+20>>2]|0)|0;i=b;return a|0}return 0}function Je(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[b+4>>2]=a;c[d>>2]=sd(20)|0;c[(c[d>>2]|0)+4>>2]=0;c[c[d>>2]>>2]=0;c[(c[d>>2]|0)+16>>2]=0;c[(c[d>>2]|0)+12>>2]=0;c[(c[d>>2]|0)+8>>2]=0;i=b;return c[d>>2]|0}function Ke(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;td(c[d>>2]|0);i=b;return}function Le(a){a=a|0;var b=0;b=i;i=i+16|0;c[b>>2]=a;i=b;return 0}function Me(a,b){a=a|0;b=b|0;var d=0;d=i;i=i+16|0;c[d+4>>2]=a;c[d>>2]=b;i=d;return}function Ne(a,b,e){a=a|0;b=b|0;e=e|0;var f=0,g=0,h=0,j=0;f=i;i=i+16|0;g=f+12|0;h=f+4|0;j=f;c[g>>2]=a;c[f+8>>2]=b;c[h>>2]=e;c[j>>2]=c[c[h>>2]>>2];if((c[(c[g>>2]|0)+12>>2]|0)==0){i=f;return}if((c[(c[g>>2]|0)+8>>2]|0)==0){i=f;return}if((c[(c[g>>2]|0)+16>>2]|0)!=0){i=f;return}e=Z(c[(c[g>>2]|0)+4>>2]|0,c[j>>2]|0)|0;if((d[(c[(c[h>>2]|0)+20>>2]|0)+(e+(c[c[g>>2]>>2]|0))|0]|0|0)==0){i=f;return}c[(c[g>>2]|0)+12>>2]=0;i=f;return}function Oe(b,e,f,g,h,j){b=b|0;e=e|0;f=f|0;g=g|0;h=h|0;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0;k=i;i=i+144|0;l=k;m=k+56|0;n=k+52|0;o=k+48|0;p=k+44|0;q=k+40|0;r=k+36|0;s=k+32|0;t=k+28|0;u=k+24|0;v=k+20|0;w=k+64|0;x=k+16|0;c[n>>2]=b;c[o>>2]=e;c[p>>2]=f;c[q>>2]=g;c[r>>2]=h;c[s>>2]=j;c[t>>2]=c[c[n>>2]>>2];c[s>>2]=c[s>>2]&-28673;c[u>>2]=(((c[q>>2]|0)+(c[(c[p>>2]|0)+12>>2]|0)-((c[(c[p>>2]|0)+12>>2]|0)/2|0)|0)/(c[(c[p>>2]|0)+12>>2]|0)|0)-1;c[v>>2]=(((c[r>>2]|0)+(c[(c[p>>2]|0)+12>>2]|0)-((c[(c[p>>2]|0)+12>>2]|0)/2|0)|0)/(c[(c[p>>2]|0)+12>>2]|0)|0)-1;if((((c[u>>2]|0)>=0?(c[u>>2]|0)<(c[t>>2]|0):0)?(c[v>>2]|0)>=0:0)?(c[v>>2]|0)<(c[t>>2]|0):0){if((c[s>>2]|0)==512){p=Z(c[v>>2]|0,c[t>>2]|0)|0;do{if((a[(c[(c[n>>2]|0)+32>>2]|0)+(p+(c[u>>2]|0))|0]|0)!=0){c[(c[o>>2]|0)+12>>2]=0}else{if((((c[u>>2]|0)==(c[c[o>>2]>>2]|0)?(c[v>>2]|0)==(c[(c[o>>2]|0)+4>>2]|0):0)?(c[(c[o>>2]|0)+12>>2]|0)!=0:0)?(c[(c[o>>2]|0)+8>>2]|0)==0:0){c[(c[o>>2]|0)+12>>2]=0;break}c[c[o>>2]>>2]=c[u>>2];c[(c[o>>2]|0)+4>>2]=c[v>>2];c[(c[o>>2]|0)+12>>2]=1;c[(c[o>>2]|0)+8>>2]=0}}while(0);c[(c[o>>2]|0)+16>>2]=0;c[m>>2]=4848;y=c[m>>2]|0;i=k;return y|0}if((c[s>>2]|0)==514){p=Z(c[v>>2]|0,c[t>>2]|0)|0;do{if((d[(c[(c[n>>2]|0)+20>>2]|0)+(p+(c[u>>2]|0))|0]|0)==0){if((((c[u>>2]|0)==(c[c[o>>2]>>2]|0)?(c[v>>2]|0)==(c[(c[o>>2]|0)+4>>2]|0):0)?(c[(c[o>>2]|0)+12>>2]|0)!=0:0)?(c[(c[o>>2]|0)+8>>2]|0)!=0:0){c[(c[o>>2]|0)+12>>2]=0;break}c[(c[o>>2]|0)+8>>2]=1;c[c[o>>2]>>2]=c[u>>2];c[(c[o>>2]|0)+4>>2]=c[v>>2];c[(c[o>>2]|0)+12>>2]=1}else{c[(c[o>>2]|0)+12>>2]=0}}while(0);c[(c[o>>2]|0)+16>>2]=0;c[m>>2]=4848;y=c[m>>2]|0;i=k;return y|0}}if((c[s>>2]|0)==521|(c[s>>2]|0)==522|(c[s>>2]|0)==524|(c[s>>2]|0)==523){he(c[s>>2]|0,c[o>>2]|0,(c[o>>2]|0)+4|0,c[t>>2]|0,c[t>>2]|0,0);c[(c[o>>2]|0)+16>>2]=1;c[(c[o>>2]|0)+12>>2]=1;c[m>>2]=4848;y=c[m>>2]|0;i=k;return y|0}if((c[(c[o>>2]|0)+12>>2]|0)!=0?(c[s>>2]|0)==525:0){c[(c[o>>2]|0)+8>>2]=1-(c[(c[o>>2]|0)+8>>2]|0);c[(c[o>>2]|0)+16>>2]=1;c[m>>2]=4848;y=c[m>>2]|0;i=k;return y|0}a:do{if((c[(c[o>>2]|0)+12>>2]|0)!=0){if(!((c[s>>2]|0)>=48&(c[s>>2]|0)<=57?((c[s>>2]|0)-48|0)<=(c[t>>2]|0):0)){z=33}do{if((z|0)==33){if((c[s>>2]|0)>=97&(c[s>>2]|0)<=122?((c[s>>2]|0)-97+10|0)<=(c[t>>2]|0):0){break}if((c[s>>2]|0)>=65&(c[s>>2]|0)<=90?((c[s>>2]|0)-65+10|0)<=(c[t>>2]|0):0){break}if(!((c[s>>2]|0)==526|(c[s>>2]|0)==8)){break a}}}while(0);c[x>>2]=(c[s>>2]|0)-48;if((c[s>>2]|0)>=65&(c[s>>2]|0)<=90){c[x>>2]=(c[s>>2]|0)-65+10}if((c[s>>2]|0)>=97&(c[s>>2]|0)<=122){c[x>>2]=(c[s>>2]|0)-97+10}if((c[s>>2]|0)==526|(c[s>>2]|0)==8){c[x>>2]=0}v=Z(c[(c[o>>2]|0)+4>>2]|0,c[t>>2]|0)|0;if((a[(c[(c[n>>2]|0)+32>>2]|0)+(v+(c[c[o>>2]>>2]|0))|0]|0)!=0){c[m>>2]=0;y=c[m>>2]|0;i=k;return y|0}if((c[(c[o>>2]|0)+8>>2]|0)!=0?(v=Z(c[(c[o>>2]|0)+4>>2]|0,c[t>>2]|0)|0,(d[(c[(c[n>>2]|0)+20>>2]|0)+(v+(c[c[o>>2]>>2]|0))|0]|0)!=0):0){c[m>>2]=0;y=c[m>>2]|0;i=k;return y|0}if((c[(c[o>>2]|0)+8>>2]|0)!=0){A=(c[x>>2]|0)>0}else{A=0}v=c[c[o>>2]>>2]|0;u=c[(c[o>>2]|0)+4>>2]|0;p=c[x>>2]|0;c[l>>2]=((A?80:82)&255)<<24>>24;c[l+4>>2]=v;c[l+8>>2]=u;c[l+12>>2]=p;ab(w|0,4856,l|0)|0;if((c[(c[o>>2]|0)+16>>2]|0)==0){c[(c[o>>2]|0)+12>>2]=0}c[m>>2]=vd(w)|0;y=c[m>>2]|0;i=k;return y|0}}while(0);if((c[s>>2]|0)==77|(c[s>>2]|0)==109){c[m>>2]=vd(4872)|0;y=c[m>>2]|0;i=k;return y|0}else{c[m>>2]=0;y=c[m>>2]|0;i=k;return y|0}return 0}function Pe(b,e){b=b|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0;f=i;i=i+64|0;g=f;h=f+48|0;j=f+44|0;k=f+40|0;l=f+36|0;m=f+32|0;n=f+28|0;o=f+24|0;p=f+20|0;q=f+16|0;r=f+12|0;c[j>>2]=b;c[k>>2]=e;c[l>>2]=c[c[j>>2]>>2];if((a[c[k>>2]|0]|0)==83){c[m>>2]=Ee(c[j>>2]|0)|0;c[(c[m>>2]|0)+40>>2]=1;c[(c[m>>2]|0)+36>>2]=1;c[q>>2]=(c[k>>2]|0)+1;c[p>>2]=0;while(1){if((c[p>>2]|0)>=(Z(c[l>>2]|0,c[l>>2]|0)|0)){s=15;break}e=(Zf(c[q>>2]|0)|0)&255;a[(c[(c[m>>2]|0)+20>>2]|0)+(c[p>>2]|0)|0]=e;if((a[c[q>>2]|0]|0)==0){s=7;break}if((d[(c[(c[m>>2]|0)+20>>2]|0)+(c[p>>2]|0)|0]|0)<1){s=7;break}if((d[(c[(c[m>>2]|0)+20>>2]|0)+(c[p>>2]|0)|0]|0)>(c[l>>2]|0)){s=7;break}while(1){if((a[c[q>>2]|0]|0)!=0){t=(rb(d[c[q>>2]|0]|0)|0)!=0}else{t=0}u=c[q>>2]|0;if(!t){break}c[q>>2]=u+1}if((a[u]|0)==44){c[q>>2]=(c[q>>2]|0)+1}c[p>>2]=(c[p>>2]|0)+1}if((s|0)==7){Fe(c[m>>2]|0);c[h>>2]=0;v=c[h>>2]|0;i=f;return v|0}else if((s|0)==15){c[h>>2]=c[m>>2];v=c[h>>2]|0;i=f;return v|0}}if(!((a[c[k>>2]|0]|0)!=80?(a[c[k>>2]|0]|0)!=82:0)){s=18}if(((((((s|0)==18?(q=(c[k>>2]|0)+1|0,c[g>>2]=n,c[g+4>>2]=o,c[g+8>>2]=p,u=(Ia(q|0,4832,g|0)|0)==3,u&(c[n>>2]|0)>=0):0)?(c[n>>2]|0)<(c[l>>2]|0):0)?(c[o>>2]|0)>=0:0)?(c[o>>2]|0)<(c[l>>2]|0):0)?(c[p>>2]|0)>=0:0)?(c[p>>2]|0)<=(c[l>>2]|0):0){c[m>>2]=Ee(c[j>>2]|0)|0;if((a[c[k>>2]|0]|0)==80?(c[p>>2]|0)>0:0){u=Z(c[o>>2]|0,c[l>>2]|0)|0;g=Z(u+(c[n>>2]|0)|0,c[l>>2]|0)|0;c[r>>2]=g+((c[p>>2]|0)-1);a[(c[(c[m>>2]|0)+28>>2]|0)+(c[r>>2]|0)|0]=((a[(c[(c[m>>2]|0)+28>>2]|0)+(c[r>>2]|0)|0]|0)!=0^1)&1}else{s=27}if(((s|0)==27?(s=Z(c[o>>2]|0,c[l>>2]|0)|0,a[(c[(c[m>>2]|0)+20>>2]|0)+(s+(c[n>>2]|0))|0]=c[p>>2],p=Z(c[o>>2]|0,c[l>>2]|0)|0,s=(c[(c[m>>2]|0)+28>>2]|0)+(Z(p+(c[n>>2]|0)|0,c[l>>2]|0)|0)|0,cg(s|0,0,c[l>>2]|0)|0,(c[(c[m>>2]|0)+36>>2]|0)==0):0)?(cf(c[l>>2]|0,c[(c[m>>2]|0)+4>>2]|0,c[(c[m>>2]|0)+8>>2]|0,c[(c[m>>2]|0)+12>>2]|0,c[(c[m>>2]|0)+20>>2]|0)|0)!=0:0){c[(c[m>>2]|0)+36>>2]=1}c[h>>2]=c[m>>2];v=c[h>>2]|0;i=f;return v|0}if((a[c[k>>2]|0]|0)!=77){c[h>>2]=0;v=c[h>>2]|0;i=f;return v|0}c[m>>2]=Ee(c[j>>2]|0)|0;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[l>>2]|0)){break}c[n>>2]=0;while(1){w=c[o>>2]|0;if((c[n>>2]|0)>=(c[l>>2]|0)){break}j=Z(w,c[l>>2]|0)|0;if((a[(c[(c[m>>2]|0)+20>>2]|0)+(j+(c[n>>2]|0))|0]|0)==0){j=Z(c[o>>2]|0,c[l>>2]|0)|0;k=(c[(c[m>>2]|0)+28>>2]|0)+(Z(j+(c[n>>2]|0)|0,c[l>>2]|0)|0)|0;cg(k|0,1,c[l>>2]|0)|0}c[n>>2]=(c[n>>2]|0)+1}c[o>>2]=w+1}c[h>>2]=c[m>>2];v=c[h>>2]|0;i=f;return v|0}function Qe(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0;f=i;i=i+32|0;g=f+20|0;h=f+16|0;j=f+12|0;k=f+8|0;l=f+4|0;m=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[m>>2]=l;c[l>>2]=c[h>>2];h=Z(c[c[g>>2]>>2]|0,c[(c[g>>2]|0)+4>>2]|0)|0;l=Z(h,c[c[m>>2]>>2]|0)|0;c[c[j>>2]>>2]=l+(((c[c[m>>2]>>2]|0)/2|0)<<1)+1;l=Z(c[c[g>>2]>>2]|0,c[(c[g>>2]|0)+4>>2]|0)|0;g=Z(l,c[c[m>>2]>>2]|0)|0;c[c[k>>2]>>2]=g+(((c[c[m>>2]>>2]|0)/2|0)<<1)+1;i=f;return}function Re(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0;f=i;i=i+16|0;g=f+8|0;h=f;c[f+12>>2]=a;c[g>>2]=b;c[f+4>>2]=d;c[h>>2]=e;c[(c[g>>2]|0)+12>>2]=c[h>>2];i=f;return}function Se(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,h=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;h=d;c[e>>2]=a;c[f>>2]=b;c[h>>2]=sd(108)|0;Nc(c[e>>2]|0,c[h>>2]|0);g[(c[h>>2]|0)+12>>2]=+g[c[h>>2]>>2]*.8999999761581421;g[(c[h>>2]|0)+16>>2]=+g[(c[h>>2]|0)+4>>2]*.8999999761581421;g[(c[h>>2]|0)+20>>2]=+g[(c[h>>2]|0)+8>>2]*.8999999761581421;g[(c[h>>2]|0)+24>>2]=0.0;g[(c[h>>2]|0)+28>>2]=0.0;g[(c[h>>2]|0)+32>>2]=0.0;g[(c[h>>2]|0)+36>>2]=0.0;g[(c[h>>2]|0)+40>>2]=0.0;g[(c[h>>2]|0)+44>>2]=0.0;g[(c[h>>2]|0)+48>>2]=0.0;g[(c[h>>2]|0)+52>>2]=+g[(c[h>>2]|0)+4>>2]*.6000000238418579;g[(c[h>>2]|0)+56>>2]=0.0;g[(c[h>>2]|0)+60>>2]=+g[c[h>>2]>>2]*.7799999713897705;g[(c[h>>2]|0)+64>>2]=+g[(c[h>>2]|0)+4>>2]*.7799999713897705;g[(c[h>>2]|0)+68>>2]=+g[(c[h>>2]|0)+8>>2]*.7799999713897705;g[(c[h>>2]|0)+72>>2]=1.0;g[(c[h>>2]|0)+76>>2]=0.0;g[(c[h>>2]|0)+80>>2]=0.0;g[(c[h>>2]|0)+84>>2]=+g[c[h>>2]>>2]*.5;g[(c[h>>2]|0)+88>>2]=+g[(c[h>>2]|0)+4>>2]*.5;g[(c[h>>2]|0)+92>>2]=+g[(c[h>>2]|0)+8>>2];g[(c[h>>2]|0)+96>>2]=+g[c[h>>2]>>2]*.5;g[(c[h>>2]|0)+100>>2]=+g[(c[h>>2]|0)+4>>2]*.5;g[(c[h>>2]|0)+104>>2]=+g[(c[h>>2]|0)+8>>2]*.10000000149011612;c[c[f>>2]>>2]=9;i=d;return c[h>>2]|0}function Te(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;g=d;c[d+12>>2]=a;c[e>>2]=b;c[f>>2]=sd(36)|0;c[g>>2]=c[c[e>>2]>>2];c[c[f>>2]>>2]=0;c[(c[f>>2]|0)+4>>2]=c[g>>2];c[(c[f>>2]|0)+8>>2]=c[(c[e>>2]|0)+12>>2];b=sd(Z(c[g>>2]|0,c[g>>2]|0)|0)|0;c[(c[f>>2]|0)+16>>2]=b;cg(c[(c[f>>2]|0)+16>>2]|0,(c[g>>2]|0)+2&255|0,Z(c[g>>2]|0,c[g>>2]|0)|0)|0;b=Z(c[g>>2]|0,c[g>>2]|0)|0;a=sd(Z(b,c[g>>2]|0)|0)|0;c[(c[f>>2]|0)+20>>2]=a;a=Z(c[g>>2]|0,c[g>>2]|0)|0;cg(c[(c[f>>2]|0)+20>>2]|0,0,Z(a,c[g>>2]|0)|0)|0;a=sd(Z(c[g>>2]|0,c[g>>2]|0)|0)|0;c[(c[f>>2]|0)+24>>2]=a;cg(c[(c[f>>2]|0)+24>>2]|0,0,Z(c[g>>2]|0,c[g>>2]|0)|0)|0;c[(c[f>>2]|0)+28>>2]=((c[g>>2]|0)*3|0)+2;if((c[(c[e>>2]|0)+8>>2]|0)==0){h=c[g>>2]|0;j=c[f>>2]|0;k=j+28|0;l=c[k>>2]|0;m=Z(h,l)|0;n=m<<2;o=sd(n)|0;p=c[f>>2]|0;q=p+32|0;c[q>>2]=o;r=c[f>>2]|0;s=r+12|0;c[s>>2]=0;t=c[f>>2]|0;i=d;return t|0}a=(c[f>>2]|0)+28|0;c[a>>2]=(c[a>>2]|0)+(c[(c[(c[e>>2]|0)+8>>2]|0)+32>>2]|0);h=c[g>>2]|0;j=c[f>>2]|0;k=j+28|0;l=c[k>>2]|0;m=Z(h,l)|0;n=m<<2;o=sd(n)|0;p=c[f>>2]|0;q=p+32|0;c[q>>2]=o;r=c[f>>2]|0;s=r+12|0;c[s>>2]=0;t=c[f>>2]|0;i=d;return t|0}function Ue(a,b){a=a|0;b=b|0;var d=0,e=0;d=i;i=i+16|0;e=d;c[d+4>>2]=a;c[e>>2]=b;td(c[(c[e>>2]|0)+24>>2]|0);td(c[(c[e>>2]|0)+20>>2]|0);td(c[(c[e>>2]|0)+16>>2]|0);td(c[(c[e>>2]|0)+32>>2]|0);td(c[e>>2]|0);i=d;return}function Ve(b,e,f,h,j,k,l,m){b=b|0;e=e|0;f=f|0;h=h|0;j=j|0;k=k|0;l=+l;m=+m;var n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0,L=0;n=i;i=i+96|0;o=n+76|0;p=n+72|0;q=n+64|0;r=n+56|0;s=n+48|0;t=n+44|0;u=n+40|0;v=n+36|0;w=n+81|0;x=n+32|0;y=n+28|0;z=n+24|0;A=n+80|0;B=n+20|0;C=n+16|0;D=n+12|0;E=n+8|0;F=n+4|0;G=n;c[o>>2]=b;c[p>>2]=e;c[n+68>>2]=f;c[q>>2]=h;c[n+60>>2]=j;c[r>>2]=k;g[n+52>>2]=l;g[s>>2]=m;c[t>>2]=c[c[q>>2]>>2];if((c[c[p>>2]>>2]|0)==0){k=Z(c[t>>2]|0,c[(c[p>>2]|0)+12>>2]|0)|0;j=Z(c[t>>2]|0,c[(c[p>>2]|0)+12>>2]|0)|0;kc(c[o>>2]|0,0,0,k+(((c[(c[p>>2]|0)+12>>2]|0)/2|0)<<1)+1|0,j+(((c[(c[p>>2]|0)+12>>2]|0)/2|0)<<1)+1|0,0);if(((c[(c[p>>2]|0)+12>>2]|0)/32|0|0)>1){H=(c[(c[p>>2]|0)+12>>2]|0)/32|0}else{H=1}if(((c[(c[p>>2]|0)+12>>2]|0)/32|0|0)>1){I=(c[(c[p>>2]|0)+12>>2]|0)/32|0}else{I=1}j=(Z(c[t>>2]|0,c[(c[p>>2]|0)+12>>2]|0)|0)+1|0;if(((c[(c[p>>2]|0)+12>>2]|0)/32|0|0)>1){J=(c[(c[p>>2]|0)+12>>2]|0)/32|0}else{J=1}k=(Z(c[t>>2]|0,c[(c[p>>2]|0)+12>>2]|0)|0)+1|0;if(((c[(c[p>>2]|0)+12>>2]|0)/32|0|0)>1){K=(c[(c[p>>2]|0)+12>>2]|0)/32|0}else{K=1}kc(c[o>>2]|0,((c[(c[p>>2]|0)+12>>2]|0)/2|0)-H|0,((c[(c[p>>2]|0)+12>>2]|0)/2|0)-I|0,j+(J<<1)|0,k+(K<<1)|0,2)}c[u>>2]=0;while(1){if((c[u>>2]|0)>=(Z(c[t>>2]|0,c[(c[p>>2]|0)+28>>2]|0)|0)){break}c[(c[(c[p>>2]|0)+32>>2]|0)+(c[u>>2]<<2)>>2]=0;c[u>>2]=(c[u>>2]|0)+1}c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[t>>2]|0)){break}c[v>>2]=0;while(1){if((c[v>>2]|0)>=(c[t>>2]|0)){break}K=Z(c[v>>2]|0,c[t>>2]|0)|0;a[w]=a[(c[(c[q>>2]|0)+20>>2]|0)+(K+(c[u>>2]|0))|0]|0;if((a[w]|0)!=0){K=Z(c[u>>2]|0,c[t>>2]|0)|0;k=(c[(c[p>>2]|0)+32>>2]|0)+(K+(d[w]|0)-1<<2)|0;c[k>>2]=(c[k>>2]|0)+1;k=Z((c[v>>2]|0)+(c[t>>2]|0)|0,c[t>>2]|0)|0;K=(c[(c[p>>2]|0)+32>>2]|0)+(k+(d[w]|0)-1<<2)|0;c[K>>2]=(c[K>>2]|0)+1;K=Z(c[v>>2]|0,c[t>>2]|0)|0;c[x>>2]=c[(c[(c[(c[q>>2]|0)+4>>2]|0)+16>>2]|0)+(K+(c[u>>2]|0)<<2)>>2];K=Z((c[x>>2]|0)+(c[t>>2]<<1)|0,c[t>>2]|0)|0;k=(c[(c[p>>2]|0)+32>>2]|0)+(K+(d[w]|0)-1<<2)|0;c[k>>2]=(c[k>>2]|0)+1;if((c[(c[p>>2]|0)+8>>2]|0)!=0){k=Z(c[v>>2]|0,c[t>>2]|0)|0;if(((k+(c[u>>2]|0)|0)%((c[t>>2]|0)+1|0)|0|0)==0){k=Z((c[t>>2]|0)*3|0,c[t>>2]|0)|0;K=(c[(c[p>>2]|0)+32>>2]|0)+(k+(d[w]|0)-1<<2)|0;c[K>>2]=(c[K>>2]|0)+1}K=Z(c[v>>2]|0,c[t>>2]|0)|0;if((((K+(c[u>>2]|0)|0)%((c[t>>2]|0)-1|0)|0|0)==0?(K=Z(c[v>>2]|0,c[t>>2]|0)|0,(K+(c[u>>2]|0)|0)>0):0)?(K=Z(c[v>>2]|0,c[t>>2]|0)|0,(K+(c[u>>2]|0)|0)<((Z(c[t>>2]|0,c[t>>2]|0)|0)-1|0)):0){K=Z(((c[t>>2]|0)*3|0)+1|0,c[t>>2]|0)|0;k=(c[(c[p>>2]|0)+32>>2]|0)+(K+(d[w]|0)-1<<2)|0;c[k>>2]=(c[k>>2]|0)+1}}if((c[(c[q>>2]|0)+8>>2]|0)!=0){k=Z(c[v>>2]|0,c[t>>2]|0)|0;c[y>>2]=c[(c[(c[(c[q>>2]|0)+8>>2]|0)+16>>2]|0)+(k+(c[u>>2]|0)<<2)>>2];k=Z((c[y>>2]|0)+((c[t>>2]|0)*3|0)+2|0,c[t>>2]|0)|0;K=(c[(c[p>>2]|0)+32>>2]|0)+(k+(d[w]|0)-1<<2)|0;c[K>>2]=(c[K>>2]|0)+1}}c[v>>2]=(c[v>>2]|0)+1}c[u>>2]=(c[u>>2]|0)+1}c[u>>2]=0;a:while(1){if((c[u>>2]|0)>=(c[t>>2]|0)){L=72;break}c[v>>2]=0;while(1){if((c[v>>2]|0)>=(c[t>>2]|0)){break}c[z>>2]=0;w=Z(c[v>>2]|0,c[t>>2]|0)|0;a[A]=a[(c[(c[q>>2]|0)+20>>2]|0)+(w+(c[u>>2]|0))|0]|0;if(+g[s>>2]>0.0?+g[s>>2]<=.13333334028720856|+g[s>>2]>=.2666666805744171:0){c[z>>2]=1}if(((c[u>>2]|0)==(c[c[r>>2]>>2]|0)?(c[v>>2]|0)==(c[(c[r>>2]|0)+4>>2]|0):0)?(c[(c[r>>2]|0)+12>>2]|0)!=0:0){c[z>>2]=(c[(c[r>>2]|0)+8>>2]|0)!=0?2:1}b:do{if((d[A]|0)!=0){w=Z(c[u>>2]|0,c[t>>2]|0)|0;do{if(((c[(c[(c[p>>2]|0)+32>>2]|0)+(w+(d[A]|0)-1<<2)>>2]|0)<=1?(y=Z((c[v>>2]|0)+(c[t>>2]|0)|0,c[t>>2]|0)|0,(c[(c[(c[p>>2]|0)+32>>2]|0)+(y+(d[A]|0)-1<<2)>>2]|0)<=1):0)?(y=Z(c[v>>2]|0,c[t>>2]|0)|0,x=Z((c[(c[(c[(c[q>>2]|0)+4>>2]|0)+16>>2]|0)+(y+(c[u>>2]|0)<<2)>>2]|0)+(c[t>>2]<<1)|0,c[t>>2]|0)|0,(c[(c[(c[p>>2]|0)+32>>2]|0)+(x+(d[A]|0)-1<<2)>>2]|0)<=1):0){if((c[(c[p>>2]|0)+8>>2]|0)!=0){x=Z(c[v>>2]|0,c[t>>2]|0)|0;if(((x+(c[u>>2]|0)|0)%((c[t>>2]|0)+1|0)|0|0)==0?(x=Z((c[t>>2]|0)*3|0,c[t>>2]|0)|0,(c[(c[(c[p>>2]|0)+32>>2]|0)+(x+(d[A]|0)-1<<2)>>2]|0)>1):0){break}x=Z(c[v>>2]|0,c[t>>2]|0)|0;if(((((x+(c[u>>2]|0)|0)%((c[t>>2]|0)-1|0)|0|0)==0?(x=Z(c[v>>2]|0,c[t>>2]|0)|0,(x+(c[u>>2]|0)|0)>0):0)?(x=Z(c[v>>2]|0,c[t>>2]|0)|0,(x+(c[u>>2]|0)|0)<((Z(c[t>>2]|0,c[t>>2]|0)|0)-1|0)):0)?(x=Z(((c[t>>2]|0)*3|0)+1|0,c[t>>2]|0)|0,(c[(c[(c[p>>2]|0)+32>>2]|0)+(x+(d[A]|0)-1<<2)>>2]|0)>1):0){break}}if((c[(c[q>>2]|0)+8>>2]|0)==0){break b}x=Z(c[v>>2]|0,c[t>>2]|0)|0;y=Z((c[(c[(c[(c[q>>2]|0)+8>>2]|0)+16>>2]|0)+(x+(c[u>>2]|0)<<2)>>2]|0)+((c[t>>2]|0)*3|0)+2|0,c[t>>2]|0)|0;if((c[(c[(c[p>>2]|0)+32>>2]|0)+(y+(d[A]|0)-1<<2)>>2]|0)<=1){break b}}}while(0);c[z>>2]=c[z>>2]|16}}while(0);if((d[A]|0)!=0?(c[(c[q>>2]|0)+8>>2]|0)!=0:0){w=Z(c[v>>2]|0,c[t>>2]|0)|0;c[C>>2]=c[(c[(c[(c[q>>2]|0)+8>>2]|0)+16>>2]|0)+(w+(c[u>>2]|0)<<2)>>2];c[D>>2]=c[(c[(c[(c[q>>2]|0)+8>>2]|0)+24>>2]|0)+(c[C>>2]<<2)>>2];c[E>>2]=0;c[F>>2]=0;c[B>>2]=0;while(1){if((c[B>>2]|0)>=(c[D>>2]|0)){break}c[G>>2]=c[(c[(c[(c[(c[q>>2]|0)+8>>2]|0)+20>>2]|0)+(c[C>>2]<<2)>>2]|0)+(c[B>>2]<<2)>>2];if((d[(c[(c[q>>2]|0)+20>>2]|0)+(c[G>>2]|0)|0]|0)==0){break}c[E>>2]=(c[E>>2]|0)+(d[(c[(c[q>>2]|0)+20>>2]|0)+(c[G>>2]|0)|0]|0);if((a[(c[(c[q>>2]|0)+24>>2]|0)+(c[G>>2]|0)|0]|0)!=0){if((c[F>>2]|0)!=0){L=62;break a}c[F>>2]=d[(c[(c[q>>2]|0)+24>>2]|0)+(c[G>>2]|0)|0]|0}c[B>>2]=(c[B>>2]|0)+1}if((c[B>>2]|0)==(c[D>>2]|0)){if((c[F>>2]|0)==0){L=67;break a}if((c[E>>2]|0)!=(c[F>>2]|0)){c[z>>2]=c[z>>2]|32}}}bf(c[o>>2]|0,c[p>>2]|0,c[q>>2]|0,c[u>>2]|0,c[v>>2]|0,c[z>>2]|0);c[v>>2]=(c[v>>2]|0)+1}c[u>>2]=(c[u>>2]|0)+1}if((L|0)==62){Ba(4752,4528,5183,4768)}else if((L|0)==67){Ba(4784,4528,5189,4768)}else if((L|0)==72){if((c[c[p>>2]>>2]|0)!=0){i=n;return}L=Z(c[t>>2]|0,c[(c[p>>2]|0)+12>>2]|0)|0;u=Z(c[t>>2]|0,c[(c[p>>2]|0)+12>>2]|0)|0;nc(c[o>>2]|0,0,0,L+(((c[(c[p>>2]|0)+12>>2]|0)/2|0)<<1)+1|0,u+(((c[(c[p>>2]|0)+12>>2]|0)/2|0)<<1)+1|0);c[c[p>>2]>>2]=1;i=n;return}}function We(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0;f=i;i=i+16|0;c[f+12>>2]=a;c[f+8>>2]=b;c[f+4>>2]=d;c[f>>2]=e;i=f;return 0.0}function Xe(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,h=0,j=0,k=0,l=0.0;f=i;i=i+32|0;h=f+16|0;j=f+12|0;k=f+8|0;c[j>>2]=a;c[k>>2]=b;c[f+4>>2]=d;c[f>>2]=e;if((((c[(c[j>>2]|0)+36>>2]|0)==0?(c[(c[k>>2]|0)+36>>2]|0)!=0:0)?(c[(c[j>>2]|0)+40>>2]|0)==0:0)?(c[(c[k>>2]|0)+40>>2]|0)==0:0){g[h>>2]=.4000000059604645;l=+g[h>>2];i=f;return+l}g[h>>2]=0.0;l=+g[h>>2];i=f;return+l}function Ye(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;i=b;return((c[(c[d>>2]|0)+36>>2]|0)!=0?1:0)|0}function Ze(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,h=0,j=0,k=0,l=0;e=i;i=i+32|0;f=e+16|0;h=e+12|0;j=e+8|0;k=e+4|0;l=e;c[f>>2]=a;c[h>>2]=b;c[j>>2]=d;Qe(c[f>>2]|0,900,k,l);g[c[h>>2]>>2]=+(c[k>>2]|0)/100.0;g[c[j>>2]>>2]=+(c[l>>2]|0)/100.0;i=e;return}function _e(b,e,f){b=b|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0;g=i;i=i+112|0;h=g;j=g+76|0;k=g+72|0;l=g+68|0;m=g+64|0;n=g+60|0;o=g+56|0;p=g+52|0;q=g+12|0;r=g+8|0;s=g+4|0;t=g+84|0;u=g+80|0;c[j>>2]=b;c[k>>2]=e;c[l>>2]=f;c[m>>2]=c[c[k>>2]>>2];c[n>>2]=tc(c[j>>2]|0,0)|0;c[q>>2]=g+16;Re(c[j>>2]|0,c[q>>2]|0,0,c[l>>2]|0);wc(c[j>>2]|0,((c[(c[q>>2]|0)+12>>2]|0)*3|0)/40|0);l=Z(c[m>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0;f=Z(c[m>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0;ge(c[j>>2]|0,(c[(c[q>>2]|0)+12>>2]|0)/2|0,(c[(c[q>>2]|0)+12>>2]|0)/2|0,l,f,c[n>>2]|0);a:do{if((c[(c[k>>2]|0)+12>>2]|0)!=0){c[s>>2]=vc(c[j>>2]|0,.8999999761581421)|0;c[r>>2]=0;while(1){if((c[r>>2]|0)>=(c[m>>2]|0)){break}f=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z(c[r>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;l=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z(c[r>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;kc(c[j>>2]|0,f,l,c[(c[q>>2]|0)+12>>2]|0,c[(c[q>>2]|0)+12>>2]|0,c[s>>2]|0);c[r>>2]=(c[r>>2]|0)+1}c[r>>2]=0;while(1){if((c[r>>2]|0)>=(c[m>>2]|0)){break a}if((c[r>>2]<<1|0)!=((c[m>>2]|0)-1|0)){l=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z(c[r>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;f=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z((c[m>>2]|0)-1-(c[r>>2]|0)|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;kc(c[j>>2]|0,l,f,c[(c[q>>2]|0)+12>>2]|0,c[(c[q>>2]|0)+12>>2]|0,c[s>>2]|0)}c[r>>2]=(c[r>>2]|0)+1}}}while(0);c[o>>2]=1;while(1){if((c[o>>2]|0)>=(c[m>>2]|0)){break}wc(c[j>>2]|0,(c[(c[q>>2]|0)+12>>2]|0)/40|0);r=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z(c[o>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;s=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z(c[o>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;f=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z(c[m>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;lc(c[j>>2]|0,r,(c[(c[q>>2]|0)+12>>2]|0)/2|0,s,f,c[n>>2]|0);c[o>>2]=(c[o>>2]|0)+1}c[p>>2]=1;while(1){v=c[j>>2]|0;w=c[(c[q>>2]|0)+12>>2]|0;if((c[p>>2]|0)>=(c[m>>2]|0)){break}wc(v,(w|0)/40|0);f=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z(c[p>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;s=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z(c[m>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;r=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z(c[p>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;lc(c[j>>2]|0,(c[(c[q>>2]|0)+12>>2]|0)/2|0,f,s,r,c[n>>2]|0);c[p>>2]=(c[p>>2]|0)+1}wc(v,(w*3|0)/40|0);af(c[j>>2]|0,c[q>>2]|0,c[k>>2]|0,c[(c[k>>2]|0)+4>>2]|0,c[n>>2]|0,0);b:do{if((c[(c[k>>2]|0)+8>>2]|0)!=0){wc(c[j>>2]|0,(c[(c[q>>2]|0)+12>>2]|0)/40|0);xc(c[j>>2]|0,1);af(c[j>>2]|0,c[q>>2]|0,c[k>>2]|0,c[(c[k>>2]|0)+8>>2]|0,c[n>>2]|0,((c[(c[q>>2]|0)+12>>2]|0)*5|0)/40|0);xc(c[j>>2]|0,0);c[p>>2]=0;while(1){if((c[p>>2]|0)>=(c[m>>2]|0)){break b}c[o>>2]=0;while(1){x=c[p>>2]|0;if((c[o>>2]|0)>=(c[m>>2]|0)){break}w=Z(x,c[m>>2]|0)|0;if((a[(c[(c[k>>2]|0)+24>>2]|0)+(w+(c[o>>2]|0))|0]|0)!=0){w=Z(c[p>>2]|0,c[m>>2]|0)|0;c[h>>2]=d[(c[(c[k>>2]|0)+24>>2]|0)+(w+(c[o>>2]|0))|0]|0;ab(t|0,4512,h|0)|0;w=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z(c[o>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;v=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z(c[p>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;jc(c[j>>2]|0,w+(((c[(c[q>>2]|0)+12>>2]|0)*7|0)/40|0)|0,v+((c[(c[q>>2]|0)+12>>2]<<4|0)/40|0)|0,1,(c[(c[q>>2]|0)+12>>2]|0)/4|0,0,c[n>>2]|0,t)}c[o>>2]=(c[o>>2]|0)+1}c[p>>2]=x+1}}}while(0);c[p>>2]=0;while(1){if((c[p>>2]|0)>=(c[m>>2]|0)){break}c[o>>2]=0;while(1){y=c[p>>2]|0;if((c[o>>2]|0)>=(c[m>>2]|0)){break}x=Z(y,c[m>>2]|0)|0;if((a[(c[(c[k>>2]|0)+20>>2]|0)+(x+(c[o>>2]|0))|0]|0)!=0){a[u+1|0]=0;x=Z(c[p>>2]|0,c[m>>2]|0)|0;a[u]=(d[(c[(c[k>>2]|0)+20>>2]|0)+(x+(c[o>>2]|0))|0]|0)+48;if((a[u]|0)>57){a[u]=(a[u]|0)+39}x=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z(c[o>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;t=((c[(c[q>>2]|0)+12>>2]|0)/2|0)+(Z(c[p>>2]|0,c[(c[q>>2]|0)+12>>2]|0)|0)|0;jc(c[j>>2]|0,x+((c[(c[q>>2]|0)+12>>2]|0)/2|0)|0,t+((c[(c[q>>2]|0)+12>>2]|0)/2|0)|0,1,(c[(c[q>>2]|0)+12>>2]|0)/2|0,257,c[n>>2]|0,u)}c[o>>2]=(c[o>>2]|0)+1}c[p>>2]=y+1}i=g;return}function $e(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0;d=i;i=i+16|0;e=d+8|0;f=d+4|0;c[f>>2]=a;c[d>>2]=b;if((c[(c[f>>2]|0)+36>>2]|0)!=0){c[e>>2]=0;g=c[e>>2]|0;i=d;return g|0}else{c[e>>2]=1;g=c[e>>2]|0;i=d;return g|0}return 0}function af(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0,L=0,M=0;h=i;i=i+112|0;j=h+104|0;k=h+100|0;l=h+96|0;m=h+92|0;n=h+88|0;o=h+84|0;p=h+80|0;q=h+76|0;r=h+72|0;s=h+68|0;t=h+64|0;u=h+60|0;v=h+56|0;w=h+52|0;x=h+48|0;y=h+44|0;z=h+40|0;A=h+36|0;B=h+32|0;C=h+28|0;D=h+24|0;E=h+20|0;F=h+16|0;G=h+12|0;H=h+8|0;I=h+4|0;J=h;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=f;c[o>>2]=g;c[p>>2]=c[c[l>>2]>>2];c[q>>2]=sd((c[p>>2]<<2)+4<<2)|0;c[r>>2]=0;a:while(1){if((c[r>>2]|0)>=(c[(c[m>>2]|0)+32>>2]|0)){K=51;break}if((c[(c[(c[m>>2]|0)+24>>2]|0)+(c[r>>2]<<2)>>2]|0)!=0){c[s>>2]=0;while(1){if((c[s>>2]|0)>=(c[p>>2]|0)){break}c[C>>2]=c[(c[(c[(c[m>>2]|0)+20>>2]|0)+(c[r>>2]<<2)>>2]|0)+(c[s>>2]<<2)>>2];if(((c[C>>2]|0)%(c[p>>2]|0)|0|0)==0){break}if((c[(c[(c[m>>2]|0)+16>>2]|0)+((c[C>>2]|0)-1<<2)>>2]|0)!=(c[r>>2]|0)){break}c[s>>2]=(c[s>>2]|0)+1}if((c[s>>2]|0)>=(c[p>>2]|0)){K=10;break}c[u>>2]=(c[(c[(c[(c[m>>2]|0)+20>>2]|0)+(c[r>>2]<<2)>>2]|0)+(c[s>>2]<<2)>>2]|0)%(c[p>>2]|0)|0;c[v>>2]=(c[(c[(c[(c[m>>2]|0)+20>>2]|0)+(c[r>>2]<<2)>>2]|0)+(c[s>>2]<<2)>>2]|0)/(c[p>>2]|0)|0;c[w>>2]=-1;c[x>>2]=0;c[y>>2]=c[u>>2];c[z>>2]=c[v>>2];c[A>>2]=c[w>>2];c[B>>2]=c[x>>2];c[t>>2]=0;while(1){c[H>>2]=0;c[F>>2]=(c[u>>2]|0)-(c[x>>2]|0)+(c[w>>2]|0);c[G>>2]=(c[v>>2]|0)+(c[w>>2]|0)+(c[x>>2]|0);if((((c[F>>2]|0)>=0?(c[F>>2]|0)<(c[p>>2]|0):0)?(c[G>>2]|0)>=0:0)?(c[G>>2]|0)<(c[p>>2]|0):0){l=Z(c[G>>2]|0,c[p>>2]|0)|0;L=(c[(c[(c[m>>2]|0)+16>>2]|0)+(l+(c[F>>2]|0)<<2)>>2]|0)==(c[r>>2]|0)}else{L=0}c[H>>2]=(c[H>>2]|0)+(L&1);c[F>>2]=(c[u>>2]|0)-(c[x>>2]|0);c[G>>2]=(c[v>>2]|0)+(c[w>>2]|0);if((((c[F>>2]|0)>=0?(c[F>>2]|0)<(c[p>>2]|0):0)?(c[G>>2]|0)>=0:0)?(c[G>>2]|0)<(c[p>>2]|0):0){l=Z(c[G>>2]|0,c[p>>2]|0)|0;M=(c[(c[(c[m>>2]|0)+16>>2]|0)+(l+(c[F>>2]|0)<<2)>>2]|0)==(c[r>>2]|0)}else{M=0}c[H>>2]=(c[H>>2]|0)+(M&1);do{if((c[H>>2]|0)!=0){if((c[H>>2]|0)==2){c[u>>2]=(c[u>>2]|0)+(c[w>>2]|0);c[v>>2]=(c[v>>2]|0)+(c[x>>2]|0);c[J>>2]=c[w>>2];c[w>>2]=c[x>>2];c[x>>2]=0-(c[J>>2]|0);c[u>>2]=(c[u>>2]|0)-(c[w>>2]|0);c[v>>2]=(c[v>>2]|0)-(c[x>>2]|0);break}else{c[u>>2]=(c[u>>2]|0)-(c[x>>2]|0);c[v>>2]=(c[v>>2]|0)+(c[w>>2]|0);break}}else{c[I>>2]=c[w>>2];c[w>>2]=0-(c[x>>2]|0);c[x>>2]=c[I>>2]}}while(0);if((c[u>>2]|0)<0){K=32;break a}if((c[u>>2]|0)>=(c[p>>2]|0)){K=32;break a}if((c[v>>2]|0)<0){K=32;break a}if((c[v>>2]|0)>=(c[p>>2]|0)){K=32;break a}l=Z(c[v>>2]|0,c[p>>2]|0)|0;if((c[(c[(c[m>>2]|0)+16>>2]|0)+(l+(c[u>>2]|0)<<2)>>2]|0)!=(c[r>>2]|0)){K=32;break a}if((((((c[u>>2]|0)+(c[w>>2]|0)|0)>=0?((c[u>>2]|0)+(c[w>>2]|0)|0)<(c[p>>2]|0):0)?((c[v>>2]|0)+(c[x>>2]|0)|0)>=0:0)?((c[v>>2]|0)+(c[x>>2]|0)|0)<(c[p>>2]|0):0)?(l=Z((c[v>>2]|0)+(c[x>>2]|0)|0,c[p>>2]|0)|0,(c[(c[(c[m>>2]|0)+16>>2]|0)+(l+((c[u>>2]|0)+(c[w>>2]|0))<<2)>>2]|0)==(c[r>>2]|0)):0){K=38;break a}if((c[t>>2]|0)>=((c[p>>2]<<1)+2|0)){K=40;break a}c[D>>2]=((c[u>>2]<<1)+1+(c[x>>2]|0)+(c[w>>2]|0)|0)/2|0;c[E>>2]=((c[v>>2]<<1)+1-(c[w>>2]|0)+(c[x>>2]|0)|0)/2|0;l=((c[(c[k>>2]|0)+12>>2]|0)/2|0)+(Z(c[D>>2]|0,c[(c[k>>2]|0)+12>>2]|0)|0)|0;c[(c[q>>2]|0)+((c[t>>2]<<1)+0<<2)>>2]=l;l=((c[(c[k>>2]|0)+12>>2]|0)/2|0)+(Z(c[E>>2]|0,c[(c[k>>2]|0)+12>>2]|0)|0)|0;c[(c[q>>2]|0)+((c[t>>2]<<1)+1<<2)>>2]=l;l=Z(c[w>>2]|0,c[o>>2]|0)|0;g=(c[q>>2]|0)+((c[t>>2]<<1)+0<<2)|0;c[g>>2]=(c[g>>2]|0)-l;l=Z(c[x>>2]|0,c[o>>2]|0)|0;g=(c[q>>2]|0)+((c[t>>2]<<1)+1<<2)|0;c[g>>2]=(c[g>>2]|0)-l;if((c[H>>2]|0)!=0){if((c[H>>2]|0)==2){l=Z(c[x>>2]|0,c[o>>2]|0)|0;g=(c[q>>2]|0)+((c[t>>2]<<1)+0<<2)|0;c[g>>2]=(c[g>>2]|0)+l;l=Z(c[w>>2]|0,c[o>>2]|0)|0;g=(c[q>>2]|0)+((c[t>>2]<<1)+1<<2)|0;c[g>>2]=(c[g>>2]|0)-l}}else{l=Z(c[x>>2]|0,c[o>>2]|0)|0;g=(c[q>>2]|0)+((c[t>>2]<<1)+0<<2)|0;c[g>>2]=(c[g>>2]|0)-l;l=Z(c[w>>2]|0,c[o>>2]|0)|0;g=(c[q>>2]|0)+((c[t>>2]<<1)+1<<2)|0;c[g>>2]=(c[g>>2]|0)+l}c[t>>2]=(c[t>>2]|0)+1;if((c[u>>2]|0)!=(c[y>>2]|0)){continue}if((c[v>>2]|0)!=(c[z>>2]|0)){continue}if((c[w>>2]|0)!=(c[A>>2]|0)){continue}if((c[x>>2]|0)==(c[B>>2]|0)){break}}mc(c[j>>2]|0,c[q>>2]|0,c[t>>2]|0,-1,c[n>>2]|0)}c[r>>2]=(c[r>>2]|0)+1}if((K|0)==10){Ba(4520,4528,5299,4536)}else if((K|0)==32){Ba(4560,4528,5372,4536)}else if((K|0)==38){Ba(4640,4528,5374,4536)}else if((K|0)==40){Ba(4736,4528,5383,4536)}else if((K|0)==51){td(c[q>>2]|0);i=h;return}}



function bf(b,e,f,h,j,k){b=b|0;e=e|0;f=f|0;h=h|0;j=j|0;k=k|0;var l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0,L=0,M=0,N=0,O=0,P=0,Q=0,R=0,S=0,T=0,U=0,V=0,W=0,X=0,Y=0,_=0,$=0,aa=0,ba=0,ca=0,da=0,ea=0,fa=0,ga=0,ha=0,ia=0,ja=0,ka=0,la=0,ma=0,na=0,oa=0,pa=0,qa=0,ra=0,sa=0,ta=0,ua=0,va=0,wa=0,xa=0,ya=0,za=0,Aa=0,Ca=0,Da=0,Ea=0,Fa=0,Ga=0,Ha=0,Ia=0,Ja=0,Ka=0,La=0,Ma=0,Na=0,Oa=0,Pa=0,Qa=0,Ra=0,Sa=0,Ta=0,Ua=0,Va=0,Wa=0,Xa=0,Ya=0,Za=0,_a=0,$a=0;l=i;i=i+240|0;m=l;n=l+212|0;o=l+208|0;p=l+204|0;q=l+200|0;r=l+196|0;s=l+192|0;t=l+188|0;u=l+184|0;v=l+180|0;w=l+176|0;x=l+172|0;y=l+168|0;z=l+164|0;A=l+160|0;B=l+156|0;C=l+152|0;D=l+216|0;E=l+128|0;F=l+124|0;G=l+120|0;H=l+116|0;I=l+112|0;J=l+108|0;K=l+104|0;L=l+100|0;M=l+96|0;N=l+92|0;O=l+88|0;P=l+84|0;Q=l+80|0;R=l+76|0;S=l+72|0;T=l+68|0;U=l+64|0;V=l+60|0;W=l+56|0;X=l+52|0;Y=l+48|0;_=l+44|0;$=l+40|0;aa=l+36|0;ba=l+32|0;ca=l+28|0;da=l+24|0;ea=l+20|0;fa=l+16|0;ga=l+12|0;ha=l+8|0;ia=l+4|0;c[n>>2]=b;c[o>>2]=e;c[p>>2]=f;c[q>>2]=h;c[r>>2]=j;c[s>>2]=k;c[t>>2]=c[c[p>>2]>>2];c[C>>2]=(c[s>>2]&32|0)!=0?6:8;k=Z(c[r>>2]|0,c[t>>2]|0)|0;j=Z(c[r>>2]|0,c[t>>2]|0)|0;if(((d[(c[(c[o>>2]|0)+16>>2]|0)+(k+(c[q>>2]|0))|0]|0)==(d[(c[(c[p>>2]|0)+20>>2]|0)+(j+(c[q>>2]|0))|0]|0)?(j=Z(c[r>>2]|0,c[t>>2]|0)|0,(d[(c[(c[o>>2]|0)+24>>2]|0)+(j+(c[q>>2]|0))|0]|0)==(c[s>>2]|0)):0)?(j=Z(c[r>>2]|0,c[t>>2]|0)|0,k=(c[(c[o>>2]|0)+20>>2]|0)+(Z(j+(c[q>>2]|0)|0,c[t>>2]|0)|0)|0,j=Z(c[r>>2]|0,c[t>>2]|0)|0,h=(c[(c[p>>2]|0)+28>>2]|0)+(Z(j+(c[q>>2]|0)|0,c[t>>2]|0)|0)|0,(_f(k,h,c[t>>2]|0)|0)==0):0){i=l;return}h=((c[(c[o>>2]|0)+12>>2]|0)/2|0)+(Z(c[q>>2]|0,c[(c[o>>2]|0)+12>>2]|0)|0)+1|0;if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){ja=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{ja=1}c[u>>2]=h+ja;ja=((c[(c[o>>2]|0)+12>>2]|0)/2|0)+(Z(c[r>>2]|0,c[(c[o>>2]|0)+12>>2]|0)|0)+1|0;if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){ka=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{ka=1}c[v>>2]=ja+ka;c[y>>2]=c[u>>2];c[z>>2]=c[v>>2];if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){la=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{la=1}ka=(c[(c[o>>2]|0)+12>>2]|0)-1-(la<<1)|0;c[w>>2]=ka;c[A>>2]=ka;if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){ma=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{ma=1}ka=(c[(c[o>>2]|0)+12>>2]|0)-1-(ma<<1)|0;c[x>>2]=ka;c[B>>2]=ka;if((c[q>>2]|0)>0?(ka=Z(c[r>>2]|0,c[t>>2]|0)|0,ma=Z(c[r>>2]|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(ka+(c[q>>2]|0)<<2)>>2]|0)==(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(ma+(c[q>>2]|0)-1<<2)>>2]|0)):0){if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){na=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{na=1}c[y>>2]=(c[y>>2]|0)-na;if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){oa=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{oa=1}c[A>>2]=(c[A>>2]|0)+oa}if(((c[q>>2]|0)+1|0)<(c[t>>2]|0)?(oa=Z(c[r>>2]|0,c[t>>2]|0)|0,na=Z(c[r>>2]|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(oa+(c[q>>2]|0)<<2)>>2]|0)==(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(na+(c[q>>2]|0)+1<<2)>>2]|0)):0){if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){pa=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{pa=1}c[A>>2]=(c[A>>2]|0)+pa}if((c[r>>2]|0)>0?(pa=Z(c[r>>2]|0,c[t>>2]|0)|0,na=Z((c[r>>2]|0)-1|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(pa+(c[q>>2]|0)<<2)>>2]|0)==(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(na+(c[q>>2]|0)<<2)>>2]|0)):0){if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){qa=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{qa=1}c[z>>2]=(c[z>>2]|0)-qa;if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){ra=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{ra=1}c[B>>2]=(c[B>>2]|0)+ra}if(((c[r>>2]|0)+1|0)<(c[t>>2]|0)?(ra=Z(c[r>>2]|0,c[t>>2]|0)|0,qa=Z((c[r>>2]|0)+1|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(ra+(c[q>>2]|0)<<2)>>2]|0)==(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(qa+(c[q>>2]|0)<<2)>>2]|0)):0){if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){sa=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{sa=1}c[B>>2]=(c[B>>2]|0)+sa}oc(c[n>>2]|0,c[y>>2]|0,c[z>>2]|0,c[A>>2]|0,c[B>>2]|0);sa=c[n>>2]|0;qa=c[y>>2]|0;ra=c[z>>2]|0;na=c[A>>2]|0;pa=c[B>>2]|0;if((c[s>>2]&15|0)==1){ta=5}else{if((c[(c[o>>2]|0)+8>>2]|0)!=0){oa=Z(c[r>>2]|0,c[t>>2]|0)|0;if(((oa+(c[q>>2]|0)|0)%((c[t>>2]|0)+1|0)|0|0)!=0){oa=Z(c[r>>2]|0,c[t>>2]|0)|0;if(((oa+(c[q>>2]|0)|0)%((c[t>>2]|0)-1|0)|0|0)==0?(oa=Z(c[r>>2]|0,c[t>>2]|0)|0,(oa+(c[q>>2]|0)|0)>0):0){oa=Z(c[r>>2]|0,c[t>>2]|0)|0;ua=(oa+(c[q>>2]|0)|0)<((Z(c[t>>2]|0,c[t>>2]|0)|0)-1|0)}else{ua=0}}else{ua=1}}else{ua=0}ta=ua?1:0}kc(sa,qa,ra,na,pa,ta);if(((c[q>>2]|0)>0?(c[r>>2]|0)>0:0)?(ta=Z(c[r>>2]|0,c[t>>2]|0)|0,pa=Z((c[r>>2]|0)-1|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(ta+(c[q>>2]|0)<<2)>>2]|0)!=(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(pa+(c[q>>2]|0)-1<<2)>>2]|0)):0){if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){va=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{va=1}if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){wa=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{wa=1}if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){xa=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{xa=1}if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){ya=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{ya=1}kc(c[n>>2]|0,(c[u>>2]|0)-va|0,(c[v>>2]|0)-wa|0,xa,ya,2)}if((((c[q>>2]|0)+1|0)<(c[t>>2]|0)?(c[r>>2]|0)>0:0)?(ya=Z(c[r>>2]|0,c[t>>2]|0)|0,xa=Z((c[r>>2]|0)-1|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(ya+(c[q>>2]|0)<<2)>>2]|0)!=(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(xa+(c[q>>2]|0)+1<<2)>>2]|0)):0){if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){za=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{za=1}if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Aa=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Aa=1}if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Ca=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Ca=1}if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Da=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Da=1}kc(c[n>>2]|0,(c[u>>2]|0)+(c[(c[o>>2]|0)+12>>2]|0)-1-(za<<1)|0,(c[v>>2]|0)-Aa|0,Ca,Da,2)}if(((c[q>>2]|0)>0?((c[r>>2]|0)+1|0)<(c[t>>2]|0):0)?(Da=Z(c[r>>2]|0,c[t>>2]|0)|0,Ca=Z((c[r>>2]|0)+1|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(Da+(c[q>>2]|0)<<2)>>2]|0)!=(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(Ca+(c[q>>2]|0)-1<<2)>>2]|0)):0){if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Ea=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Ea=1}if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Fa=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Fa=1}if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Ga=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Ga=1}if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Ha=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Ha=1}kc(c[n>>2]|0,(c[u>>2]|0)-Ea|0,(c[v>>2]|0)+(c[(c[o>>2]|0)+12>>2]|0)-1-(Fa<<1)|0,Ga,Ha,2)}if((((c[q>>2]|0)+1|0)<(c[t>>2]|0)?((c[r>>2]|0)+1|0)<(c[t>>2]|0):0)?(Ha=Z(c[r>>2]|0,c[t>>2]|0)|0,Ga=Z((c[r>>2]|0)+1|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(Ha+(c[q>>2]|0)<<2)>>2]|0)!=(c[(c[(c[(c[p>>2]|0)+4>>2]|0)+16>>2]|0)+(Ga+(c[q>>2]|0)+1<<2)>>2]|0)):0){if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Ia=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Ia=1}if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Ja=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Ja=1}if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Ka=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Ka=1}if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){La=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{La=1}kc(c[n>>2]|0,(c[u>>2]|0)+(c[(c[o>>2]|0)+12>>2]|0)-1-(Ia<<1)|0,(c[v>>2]|0)+(c[(c[o>>2]|0)+12>>2]|0)-1-(Ja<<1)|0,Ka,La,2)}if((c[s>>2]&15|0)==2){c[E>>2]=c[y>>2];c[E+4>>2]=c[z>>2];c[E+8>>2]=(c[y>>2]|0)+((c[A>>2]|0)/2|0);c[E+12>>2]=c[z>>2];c[E+16>>2]=c[y>>2];c[E+20>>2]=(c[z>>2]|0)+((c[B>>2]|0)/2|0);mc(c[n>>2]|0,E,3,5,5)}if((c[(c[p>>2]|0)+8>>2]|0)!=0){if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Ma=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Ma=1}c[F>>2]=Ma*3;c[O>>2]=0;c[P>>2]=0;c[Q>>2]=0;c[R>>2]=0;if((c[(c[(c[p>>2]|0)+4>>2]|0)+8>>2]|0)==1){c[G>>2]=c[u>>2];c[H>>2]=c[v>>2];c[I>>2]=c[w>>2];c[J>>2]=c[x>>2]}else{c[G>>2]=c[y>>2];c[H>>2]=c[z>>2];c[I>>2]=c[A>>2];c[J>>2]=c[B>>2]}c[K>>2]=(c[G>>2]|0)-1;c[L>>2]=(c[H>>2]|0)-1;c[M>>2]=(c[G>>2]|0)+(c[I>>2]|0);c[N>>2]=(c[H>>2]|0)+(c[J>>2]|0);if(!((c[q>>2]|0)!=0?(x=Z(c[r>>2]|0,c[t>>2]|0)|0,w=Z(c[r>>2]|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(x+(c[q>>2]|0)<<2)>>2]|0)==(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(w+(c[q>>2]|0)-1<<2)>>2]|0)):0)){c[O>>2]=1;c[K>>2]=(c[K>>2]|0)+(c[F>>2]|0)}if(!(((c[q>>2]|0)+1|0)<(c[t>>2]|0)?(w=Z(c[r>>2]|0,c[t>>2]|0)|0,x=Z(c[r>>2]|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(w+(c[q>>2]|0)<<2)>>2]|0)==(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(x+(c[q>>2]|0)+1<<2)>>2]|0)):0)){c[P>>2]=1;c[M>>2]=(c[M>>2]|0)-(c[F>>2]|0)}if(!((c[r>>2]|0)!=0?(x=Z(c[r>>2]|0,c[t>>2]|0)|0,w=Z((c[r>>2]|0)-1|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(x+(c[q>>2]|0)<<2)>>2]|0)==(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(w+(c[q>>2]|0)<<2)>>2]|0)):0)){c[Q>>2]=1;c[L>>2]=(c[L>>2]|0)+(c[F>>2]|0)}if(!(((c[r>>2]|0)+1|0)<(c[t>>2]|0)?(w=Z(c[r>>2]|0,c[t>>2]|0)|0,x=Z((c[r>>2]|0)+1|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(w+(c[q>>2]|0)<<2)>>2]|0)==(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(x+(c[q>>2]|0)<<2)>>2]|0)):0)){c[R>>2]=1;c[N>>2]=(c[N>>2]|0)-(c[F>>2]|0)}if((c[Q>>2]|0)!=0){lc(c[n>>2]|0,c[K>>2]|0,c[L>>2]|0,c[M>>2]|0,c[L>>2]|0,c[C>>2]|0)}if((c[R>>2]|0)!=0){lc(c[n>>2]|0,c[K>>2]|0,c[N>>2]|0,c[M>>2]|0,c[N>>2]|0,c[C>>2]|0)}if((c[O>>2]|0)!=0){lc(c[n>>2]|0,c[K>>2]|0,c[L>>2]|0,c[K>>2]|0,c[N>>2]|0,c[C>>2]|0)}if((c[P>>2]|0)!=0){lc(c[n>>2]|0,c[M>>2]|0,c[L>>2]|0,c[M>>2]|0,c[N>>2]|0,c[C>>2]|0)}if(((((c[q>>2]|0)>0?(c[r>>2]|0)>0:0)?(c[O>>2]|0)==0:0)?(c[Q>>2]|0)==0:0)?(N=Z(c[r>>2]|0,c[t>>2]|0)|0,M=Z((c[r>>2]|0)-1|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(N+(c[q>>2]|0)<<2)>>2]|0)!=(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(M+(c[q>>2]|0)-1<<2)>>2]|0)):0){lc(c[n>>2]|0,c[K>>2]|0,(c[L>>2]|0)+(c[F>>2]|0)|0,(c[K>>2]|0)+(c[F>>2]|0)|0,(c[L>>2]|0)+(c[F>>2]|0)|0,c[C>>2]|0);lc(c[n>>2]|0,(c[K>>2]|0)+(c[F>>2]|0)|0,c[L>>2]|0,(c[K>>2]|0)+(c[F>>2]|0)|0,(c[L>>2]|0)+(c[F>>2]|0)|0,c[C>>2]|0)}if((((((c[q>>2]|0)+1|0)<(c[t>>2]|0)?(c[r>>2]|0)>0:0)?(c[P>>2]|0)==0:0)?(c[Q>>2]|0)==0:0)?(Q=Z(c[r>>2]|0,c[t>>2]|0)|0,M=Z((c[r>>2]|0)-1|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(Q+(c[q>>2]|0)<<2)>>2]|0)!=(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(M+(c[q>>2]|0)+1<<2)>>2]|0)):0){lc(c[n>>2]|0,(c[G>>2]|0)+(c[I>>2]|0)-(c[F>>2]|0)|0,(c[L>>2]|0)+(c[F>>2]|0)|0,(c[G>>2]|0)+(c[I>>2]|0)|0,(c[L>>2]|0)+(c[F>>2]|0)|0,c[C>>2]|0);lc(c[n>>2]|0,(c[G>>2]|0)+(c[I>>2]|0)-(c[F>>2]|0)|0,c[L>>2]|0,(c[G>>2]|0)+(c[I>>2]|0)-(c[F>>2]|0)|0,(c[L>>2]|0)+(c[F>>2]|0)|0,c[C>>2]|0)}if(((((c[q>>2]|0)>0?((c[r>>2]|0)+1|0)<(c[t>>2]|0):0)?(c[O>>2]|0)==0:0)?(c[R>>2]|0)==0:0)?(O=Z(c[r>>2]|0,c[t>>2]|0)|0,L=Z((c[r>>2]|0)+1|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(O+(c[q>>2]|0)<<2)>>2]|0)!=(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(L+(c[q>>2]|0)-1<<2)>>2]|0)):0){lc(c[n>>2]|0,c[K>>2]|0,(c[H>>2]|0)+(c[J>>2]|0)-(c[F>>2]|0)|0,(c[K>>2]|0)+(c[F>>2]|0)|0,(c[H>>2]|0)+(c[J>>2]|0)-(c[F>>2]|0)|0,c[C>>2]|0);lc(c[n>>2]|0,(c[K>>2]|0)+(c[F>>2]|0)|0,(c[H>>2]|0)+(c[J>>2]|0)-(c[F>>2]|0)|0,(c[K>>2]|0)+(c[F>>2]|0)|0,(c[H>>2]|0)+(c[J>>2]|0)|0,c[C>>2]|0)}if((((((c[q>>2]|0)+1|0)<(c[t>>2]|0)?((c[r>>2]|0)+1|0)<(c[t>>2]|0):0)?(c[P>>2]|0)==0:0)?(c[R>>2]|0)==0:0)?(R=Z(c[r>>2]|0,c[t>>2]|0)|0,P=Z((c[r>>2]|0)+1|0,c[t>>2]|0)|0,(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(R+(c[q>>2]|0)<<2)>>2]|0)!=(c[(c[(c[(c[p>>2]|0)+8>>2]|0)+16>>2]|0)+(P+(c[q>>2]|0)+1<<2)>>2]|0)):0){lc(c[n>>2]|0,(c[G>>2]|0)+(c[I>>2]|0)-(c[F>>2]|0)|0,(c[H>>2]|0)+(c[J>>2]|0)-(c[F>>2]|0)|0,(c[G>>2]|0)+(c[I>>2]|0)-(c[F>>2]|0)|0,(c[H>>2]|0)+(c[J>>2]|0)|0,c[C>>2]|0);lc(c[n>>2]|0,(c[G>>2]|0)+(c[I>>2]|0)-(c[F>>2]|0)|0,(c[H>>2]|0)+(c[J>>2]|0)-(c[F>>2]|0)|0,(c[G>>2]|0)+(c[I>>2]|0)|0,(c[H>>2]|0)+(c[J>>2]|0)-(c[F>>2]|0)|0,c[C>>2]|0)}}if((c[(c[p>>2]|0)+16>>2]|0)!=0?(F=Z(c[r>>2]|0,c[t>>2]|0)|0,(d[(c[(c[p>>2]|0)+24>>2]|0)+(F+(c[q>>2]|0))|0]|0)!=0):0){F=Z(c[r>>2]|0,c[t>>2]|0)|0;c[m>>2]=d[(c[(c[p>>2]|0)+24>>2]|0)+(F+(c[q>>2]|0))|0]|0;ab(D|0,4512,m|0)|0;if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Na=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Na=1}if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Oa=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Oa=1}jc(c[n>>2]|0,(c[u>>2]|0)+(Na<<2)|0,(c[v>>2]|0)+(Oa<<2)+((c[(c[o>>2]|0)+12>>2]|0)/4|0)|0,1,(c[(c[o>>2]|0)+12>>2]|0)/4|0,0,c[C>>2]|0,D)}C=Z(c[r>>2]|0,c[t>>2]|0)|0;a:do{if((a[(c[(c[p>>2]|0)+20>>2]|0)+(C+(c[q>>2]|0))|0]|0)==0){c[U>>2]=0;c[S>>2]=0;while(1){if((c[S>>2]|0)>=(c[t>>2]|0)){break}Oa=Z(c[r>>2]|0,c[t>>2]|0)|0;Na=Z(Oa+(c[q>>2]|0)|0,c[t>>2]|0)|0;if((a[(c[(c[p>>2]|0)+28>>2]|0)+(Na+(c[S>>2]|0))|0]|0)!=0){c[U>>2]=(c[U>>2]|0)+1}c[S>>2]=(c[S>>2]|0)+1}if((c[U>>2]|0)!=0){c[ba>>2]=2;if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Pa=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Pa=1}c[V>>2]=(c[u>>2]|0)+Pa;if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Qa=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Qa=1}c[W>>2]=(c[V>>2]|0)+(c[(c[o>>2]|0)+12>>2]|0)-Qa;if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Ra=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Ra=1}c[X>>2]=(c[v>>2]|0)+Ra;if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Sa=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Sa=1}c[Y>>2]=(c[X>>2]|0)+(c[(c[o>>2]|0)+12>>2]|0)-Sa;if((c[(c[p>>2]|0)+16>>2]|0)!=0){if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Ta=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Ta=1}c[V>>2]=(c[V>>2]|0)+(Ta*3|0);if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Ua=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Ua=1}c[W>>2]=(c[W>>2]|0)-(Ua*3|0);if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Va=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Va=1}c[X>>2]=(c[X>>2]|0)+(Va*3|0);if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Wa=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Wa=1}c[Y>>2]=(c[Y>>2]|0)-(Wa*3|0);Na=Z(c[r>>2]|0,c[t>>2]|0)|0;if((d[(c[(c[p>>2]|0)+24>>2]|0)+(Na+(c[q>>2]|0))|0]|0)!=0){c[X>>2]=(c[X>>2]|0)+((c[(c[o>>2]|0)+12>>2]|0)/4|0)}}g[_>>2]=0.0;c[ca>>2]=0;c[$>>2]=3;while(1){if((c[$>>2]|0)>=(((c[U>>2]|0)>4?c[U>>2]|0:4)|0)){break}c[aa>>2]=((c[U>>2]|0)+(c[$>>2]|0)-1|0)/(c[$>>2]|0)|0;c[aa>>2]=(c[aa>>2]|0)>(c[ba>>2]|0)?c[aa>>2]|0:c[ba>>2]|0;g[ea>>2]=+((c[W>>2]|0)-(c[V>>2]|0)|0)/+(c[$>>2]|0);g[fa>>2]=+((c[Y>>2]|0)-(c[X>>2]|0)|0)/+(c[aa>>2]|0);g[ga>>2]=+g[ea>>2]<+g[fa>>2]?+g[ea>>2]:+g[fa>>2];if(+g[ga>>2]>+g[_>>2]){g[_>>2]=+g[ga>>2];c[ca>>2]=c[$>>2]}c[$>>2]=(c[$>>2]|0)+1}if((c[ca>>2]|0)<=0){Ba(4800,4528,5019,4816)}c[$>>2]=c[ca>>2];c[aa>>2]=((c[U>>2]|0)+(c[$>>2]|0)-1|0)/(c[$>>2]|0)|0;c[aa>>2]=(c[aa>>2]|0)>(c[ba>>2]|0)?c[aa>>2]|0:c[ba>>2]|0;if((((c[W>>2]|0)-(c[V>>2]|0)|0)/(c[$>>2]|0)|0|0)<(((c[Y>>2]|0)-(c[X>>2]|0)|0)/(c[aa>>2]|0)|0|0)){Xa=((c[W>>2]|0)-(c[V>>2]|0)|0)/(c[$>>2]|0)|0}else{Xa=((c[Y>>2]|0)-(c[X>>2]|0)|0)/(c[aa>>2]|0)|0}c[da>>2]=Xa;c[V>>2]=(c[u>>2]|0)+(((c[(c[o>>2]|0)+12>>2]|0)-(Z(c[da>>2]|0,c[$>>2]|0)|0)|0)/2|0);c[X>>2]=(c[v>>2]|0)+(((c[(c[o>>2]|0)+12>>2]|0)-(Z(c[da>>2]|0,c[aa>>2]|0)|0)|0)/2|0);if((c[(c[p>>2]|0)+16>>2]|0)!=0?(Na=Z(c[r>>2]|0,c[t>>2]|0)|0,(d[(c[(c[p>>2]|0)+24>>2]|0)+(Na+(c[q>>2]|0))|0]|0)!=0):0){if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){Ya=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{Ya=1}if((c[X>>2]|0)>((c[v>>2]|0)+(Ya*3|0)+((c[(c[o>>2]|0)+12>>2]|0)/4|0)|0)){Za=c[X>>2]|0}else{if(((c[(c[o>>2]|0)+12>>2]|0)/32|0|0)>1){_a=(c[(c[o>>2]|0)+12>>2]|0)/32|0}else{_a=1}Za=(c[v>>2]|0)+(_a*3|0)+((c[(c[o>>2]|0)+12>>2]|0)/4|0)|0}c[X>>2]=Za}c[T>>2]=0;c[S>>2]=0;while(1){if((c[S>>2]|0)>=(c[t>>2]|0)){break a}Na=Z(c[r>>2]|0,c[t>>2]|0)|0;Oa=Z(Na+(c[q>>2]|0)|0,c[t>>2]|0)|0;if((a[(c[(c[p>>2]|0)+28>>2]|0)+(Oa+(c[S>>2]|0))|0]|0)!=0){c[ha>>2]=(c[T>>2]|0)%(c[$>>2]|0)|0;c[ia>>2]=(c[T>>2]|0)/(c[$>>2]|0)|0;a[D+1|0]=0;a[D]=(c[S>>2]|0)+49;if((a[D]|0)>57){a[D]=(a[D]|0)+39}Oa=(c[V>>2]|0)+((Z(c[da>>2]|0,(c[ha>>2]<<1)+1|0)|0)/2|0)|0;Na=(c[X>>2]|0)+((Z(c[da>>2]|0,(c[ia>>2]<<1)+1|0)|0)/2|0)|0;jc(c[n>>2]|0,Oa,Na,1,c[da>>2]|0,257,7,D);c[T>>2]=(c[T>>2]|0)+1}c[S>>2]=(c[S>>2]|0)+1}}}else{a[D+1|0]=0;Na=Z(c[r>>2]|0,c[t>>2]|0)|0;a[D]=(d[(c[(c[p>>2]|0)+20>>2]|0)+(Na+(c[q>>2]|0))|0]|0)+48;if((a[D]|0)>57){a[D]=(a[D]|0)+39}Na=Z(c[r>>2]|0,c[t>>2]|0)|0;if((d[(c[(c[p>>2]|0)+32>>2]|0)+(Na+(c[q>>2]|0))|0]|0)!=0){$a=3}else{$a=(c[s>>2]&16|0)!=0?6:4}jc(c[n>>2]|0,(c[u>>2]|0)+((c[(c[o>>2]|0)+12>>2]|0)/2|0)|0,(c[v>>2]|0)+((c[(c[o>>2]|0)+12>>2]|0)/2|0)|0,1,(c[(c[o>>2]|0)+12>>2]|0)/2|0,257,$a,D)}}while(0);pc(c[n>>2]|0);nc(c[n>>2]|0,c[y>>2]|0,c[z>>2]|0,c[A>>2]|0,c[B>>2]|0);B=Z(c[r>>2]|0,c[t>>2]|0)|0;A=Z(c[r>>2]|0,c[t>>2]|0)|0;a[(c[(c[o>>2]|0)+16>>2]|0)+(A+(c[q>>2]|0))|0]=a[(c[(c[p>>2]|0)+20>>2]|0)+(B+(c[q>>2]|0))|0]|0;B=Z(c[r>>2]|0,c[t>>2]|0)|0;A=(c[(c[o>>2]|0)+20>>2]|0)+(Z(B+(c[q>>2]|0)|0,c[t>>2]|0)|0)|0;B=Z(c[r>>2]|0,c[t>>2]|0)|0;z=(c[(c[p>>2]|0)+28>>2]|0)+(Z(B+(c[q>>2]|0)|0,c[t>>2]|0)|0)|0;eg(A|0,z|0,c[t>>2]|0)|0;z=Z(c[r>>2]|0,c[t>>2]|0)|0;a[(c[(c[o>>2]|0)+24>>2]|0)+(z+(c[q>>2]|0))|0]=c[s>>2];i=l;return}function cf(b,e,f,g,h){b=b|0;e=e|0;f=f|0;g=g|0;h=h|0;var j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0;j=i;i=i+48|0;k=j+44|0;l=j+40|0;m=j+36|0;n=j+32|0;o=j+28|0;p=j+24|0;q=j+20|0;r=j+16|0;s=j+12|0;t=j+8|0;u=j+4|0;v=j;c[l>>2]=b;c[m>>2]=e;c[n>>2]=f;c[o>>2]=g;c[p>>2]=h;c[q>>2]=sd(c[l>>2]|0)|0;c[s>>2]=0;a:while(1){if((c[s>>2]|0)>=(c[l>>2]|0)){break}cg(c[q>>2]|0,0,c[l>>2]|0)|0;c[r>>2]=0;while(1){if((c[r>>2]|0)>=(c[l>>2]|0)){break}h=Z(c[s>>2]|0,c[l>>2]|0)|0;if((d[(c[p>>2]|0)+(h+(c[r>>2]|0))|0]|0)>0?(h=Z(c[s>>2]|0,c[l>>2]|0)|0,(d[(c[p>>2]|0)+(h+(c[r>>2]|0))|0]|0)<=(c[l>>2]|0)):0){h=Z(c[s>>2]|0,c[l>>2]|0)|0;a[(c[q>>2]|0)+((d[(c[p>>2]|0)+(h+(c[r>>2]|0))|0]|0)-1)|0]=1}c[r>>2]=(c[r>>2]|0)+1}c[v>>2]=0;while(1){if((c[v>>2]|0)>=(c[l>>2]|0)){break}if((a[(c[q>>2]|0)+(c[v>>2]|0)|0]|0)==0){w=12;break a}c[v>>2]=(c[v>>2]|0)+1}c[s>>2]=(c[s>>2]|0)+1}if((w|0)==12){td(c[q>>2]|0);c[k>>2]=0;x=c[k>>2]|0;i=j;return x|0}c[r>>2]=0;b:while(1){if((c[r>>2]|0)>=(c[l>>2]|0)){break}cg(c[q>>2]|0,0,c[l>>2]|0)|0;c[s>>2]=0;while(1){if((c[s>>2]|0)>=(c[l>>2]|0)){break}h=Z(c[s>>2]|0,c[l>>2]|0)|0;if((d[(c[p>>2]|0)+(h+(c[r>>2]|0))|0]|0)>0?(h=Z(c[s>>2]|0,c[l>>2]|0)|0,(d[(c[p>>2]|0)+(h+(c[r>>2]|0))|0]|0)<=(c[l>>2]|0)):0){h=Z(c[s>>2]|0,c[l>>2]|0)|0;a[(c[q>>2]|0)+((d[(c[p>>2]|0)+(h+(c[r>>2]|0))|0]|0)-1)|0]=1}c[s>>2]=(c[s>>2]|0)+1}c[v>>2]=0;while(1){if((c[v>>2]|0)>=(c[l>>2]|0)){break}if((a[(c[q>>2]|0)+(c[v>>2]|0)|0]|0)==0){w=26;break b}c[v>>2]=(c[v>>2]|0)+1}c[r>>2]=(c[r>>2]|0)+1}if((w|0)==26){td(c[q>>2]|0);c[k>>2]=0;x=c[k>>2]|0;i=j;return x|0}c[t>>2]=0;c:while(1){if((c[t>>2]|0)>=(c[l>>2]|0)){break}cg(c[q>>2]|0,0,c[l>>2]|0)|0;c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[l>>2]|0)){break}if((d[(c[p>>2]|0)+(c[(c[(c[(c[m>>2]|0)+20>>2]|0)+(c[t>>2]<<2)>>2]|0)+(c[u>>2]<<2)>>2]|0)|0]|0)>0?(d[(c[p>>2]|0)+(c[(c[(c[(c[m>>2]|0)+20>>2]|0)+(c[t>>2]<<2)>>2]|0)+(c[u>>2]<<2)>>2]|0)|0]|0)<=(c[l>>2]|0):0){a[(c[q>>2]|0)+((d[(c[p>>2]|0)+(c[(c[(c[(c[m>>2]|0)+20>>2]|0)+(c[t>>2]<<2)>>2]|0)+(c[u>>2]<<2)>>2]|0)|0]|0)-1)|0]=1}c[u>>2]=(c[u>>2]|0)+1}c[v>>2]=0;while(1){if((c[v>>2]|0)>=(c[l>>2]|0)){break}if((a[(c[q>>2]|0)+(c[v>>2]|0)|0]|0)==0){w=40;break c}c[v>>2]=(c[v>>2]|0)+1}c[t>>2]=(c[t>>2]|0)+1}if((w|0)==40){td(c[q>>2]|0);c[k>>2]=0;x=c[k>>2]|0;i=j;return x|0}d:do{if((c[n>>2]|0)!=0){c[t>>2]=0;e:while(1){if((c[t>>2]|0)>=(c[(c[n>>2]|0)+32>>2]|0)){break d}cg(c[q>>2]|0,0,c[l>>2]|0)|0;c[u>>2]=0;while(1){if((c[u>>2]|0)>=(c[(c[(c[n>>2]|0)+24>>2]|0)+(c[t>>2]<<2)>>2]|0)){break}if((d[(c[p>>2]|0)+(c[(c[(c[(c[n>>2]|0)+20>>2]|0)+(c[t>>2]<<2)>>2]|0)+(c[u>>2]<<2)>>2]|0)|0]|0)>0?(d[(c[p>>2]|0)+(c[(c[(c[(c[n>>2]|0)+20>>2]|0)+(c[t>>2]<<2)>>2]|0)+(c[u>>2]<<2)>>2]|0)|0]|0)<=(c[l>>2]|0):0){if((a[(c[q>>2]|0)+((d[(c[p>>2]|0)+(c[(c[(c[(c[n>>2]|0)+20>>2]|0)+(c[t>>2]<<2)>>2]|0)+(c[u>>2]<<2)>>2]|0)|0]|0)-1)|0]|0)!=0){break e}a[(c[q>>2]|0)+((d[(c[p>>2]|0)+(c[(c[(c[(c[n>>2]|0)+20>>2]|0)+(c[t>>2]<<2)>>2]|0)+(c[u>>2]<<2)>>2]|0)|0]|0)-1)|0]=1}c[u>>2]=(c[u>>2]|0)+1}c[t>>2]=(c[t>>2]|0)+1}td(c[q>>2]|0);c[k>>2]=0;x=c[k>>2]|0;i=j;return x|0}}while(0);f:do{if((c[o>>2]|0)!=0){cg(c[q>>2]|0,0,c[l>>2]|0)|0;c[t>>2]=0;while(1){if((c[t>>2]|0)>=(c[l>>2]|0)){break}u=Z(c[t>>2]|0,(c[l>>2]|0)+1|0)|0;if((d[(c[p>>2]|0)+u|0]|0)>0?(u=Z(c[t>>2]|0,(c[l>>2]|0)+1|0)|0,(d[(c[p>>2]|0)+u|0]|0)<=(c[l>>2]|0)):0){u=Z(c[t>>2]|0,(c[l>>2]|0)+1|0)|0;a[(c[q>>2]|0)+((d[(c[p>>2]|0)+u|0]|0)-1)|0]=1}c[t>>2]=(c[t>>2]|0)+1}c[v>>2]=0;while(1){if((c[v>>2]|0)>=(c[l>>2]|0)){break}if((a[(c[q>>2]|0)+(c[v>>2]|0)|0]|0)==0){w=65;break}c[v>>2]=(c[v>>2]|0)+1}if((w|0)==65){td(c[q>>2]|0);c[k>>2]=0;x=c[k>>2]|0;i=j;return x|0}c[t>>2]=0;while(1){if((c[t>>2]|0)>=(c[l>>2]|0)){break}u=Z((c[t>>2]|0)+1|0,(c[l>>2]|0)-1|0)|0;if((d[(c[p>>2]|0)+u|0]|0)>0?(u=Z((c[t>>2]|0)+1|0,(c[l>>2]|0)-1|0)|0,(d[(c[p>>2]|0)+u|0]|0)<=(c[l>>2]|0)):0){u=Z((c[t>>2]|0)+1|0,(c[l>>2]|0)-1|0)|0;a[(c[q>>2]|0)+((d[(c[p>>2]|0)+u|0]|0)-1)|0]=1}c[t>>2]=(c[t>>2]|0)+1}c[v>>2]=0;while(1){if((c[v>>2]|0)>=(c[l>>2]|0)){break f}if((a[(c[q>>2]|0)+(c[v>>2]|0)|0]|0)==0){break}c[v>>2]=(c[v>>2]|0)+1}td(c[q>>2]|0);c[k>>2]=0;x=c[k>>2]|0;i=j;return x|0}}while(0);td(c[q>>2]|0);c[k>>2]=1;x=c[k>>2]|0;i=j;return x|0}function df(b,e,f,g){b=b|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0;h=i;i=i+80|0;j=h+68|0;k=h+64|0;l=h+60|0;m=h+56|0;n=h+52|0;o=h+48|0;p=h+44|0;q=h+40|0;r=h+36|0;s=h+32|0;t=h+28|0;u=h+24|0;v=h+20|0;w=h+73|0;x=h+72|0;y=h+16|0;z=h+12|0;A=h+8|0;B=h+4|0;C=h;c[j>>2]=b;c[k>>2]=e;c[l>>2]=f;c[m>>2]=g;if((c[(c[k>>2]|0)+8>>2]|0)!=1){c[n>>2]=c[(c[k>>2]|0)+8>>2];c[o>>2]=c[(c[k>>2]|0)+4>>2]}else{c[o>>2]=1;c[n>>2]=1}c[s>>2]=(c[j>>2]|0)+(((c[j>>2]|0)-1|0)/(c[n>>2]|0)|0)<<1;c[t>>2]=(c[j>>2]|0)+(((c[j>>2]|0)-1|0)/(c[o>>2]|0)|0);c[r>>2]=Z(c[s>>2]|0,c[t>>2]|0)|0;c[u>>2]=sd((c[r>>2]|0)+1|0)|0;c[v>>2]=c[u>>2];c[q>>2]=0;while(1){if((c[q>>2]|0)>=(c[j>>2]|0)){break}c[p>>2]=0;while(1){D=c[q>>2]|0;E=c[j>>2]|0;if((c[p>>2]|0)>=(c[j>>2]|0)){break}t=Z(D,E)|0;a[x]=a[(c[m>>2]|0)+(t+(c[p>>2]|0))|0]|0;a:do{if((d[x]|0|0)!=0){t=d[x]|0;if((d[x]|0|0)<=9){a[w]=48+t;break}else{a[w]=97+t-10;break}}else{do{if((c[l>>2]|0)!=0){t=Z(c[q>>2]|0,c[j>>2]|0)|0;if(((t+(c[p>>2]|0)|0)%((c[j>>2]|0)+1|0)|0|0)!=0){t=Z(c[q>>2]|0,c[j>>2]|0)|0;if(((t+(c[p>>2]|0)|0)%((c[j>>2]|0)-1|0)|0|0)!=0){break}t=Z(c[q>>2]|0,c[j>>2]|0)|0;if((t+(c[p>>2]|0)|0)<=0){break}t=Z(c[q>>2]|0,c[j>>2]|0)|0;if((t+(c[p>>2]|0)|0)>=((Z(c[j>>2]|0,c[j>>2]|0)|0)-1|0)){break}}a[w]=95;break a}}while(0);a[w]=46}}while(0);t=a[w]|0;s=c[v>>2]|0;c[v>>2]=s+1;a[s]=t;t=(c[p>>2]|0)==((c[j>>2]|0)-1|0);s=c[v>>2]|0;c[v>>2]=s+1;if(!t){a[s]=32;if((((c[p>>2]|0)+1|0)%(c[n>>2]|0)|0|0)==0){t=Z(c[q>>2]|0,c[j>>2]|0)|0;g=Z(c[q>>2]|0,c[j>>2]|0)|0;if((c[(c[(c[k>>2]|0)+16>>2]|0)+(t+(c[p>>2]|0)<<2)>>2]|0)!=(c[(c[(c[k>>2]|0)+16>>2]|0)+(g+(c[p>>2]|0)+1<<2)>>2]|0)){a[w]=124}else{a[w]=32}g=a[w]|0;t=c[v>>2]|0;c[v>>2]=t+1;a[t]=g;g=c[v>>2]|0;c[v>>2]=g+1;a[g]=32}}else{a[s]=10}c[p>>2]=(c[p>>2]|0)+1}b:do{if((D|0)!=(E-1|0)?(((c[q>>2]|0)+1|0)%(c[o>>2]|0)|0|0)==0:0){c[p>>2]=0;while(1){if((c[p>>2]|0)>=(c[j>>2]|0)){break b}c[y>>2]=2;if((c[p>>2]|0)==((c[j>>2]|0)-1|0)){c[y>>2]=(c[y>>2]|0)+ -1}if((c[p>>2]|0)>0?((c[p>>2]|0)%(c[n>>2]|0)|0|0)==0:0){c[y>>2]=(c[y>>2]|0)+1}s=Z(c[q>>2]|0,c[j>>2]|0)|0;g=Z((c[q>>2]|0)+1|0,c[j>>2]|0)|0;if((c[(c[(c[k>>2]|0)+16>>2]|0)+(s+(c[p>>2]|0)<<2)>>2]|0)!=(c[(c[(c[k>>2]|0)+16>>2]|0)+(g+(c[p>>2]|0)<<2)>>2]|0)){a[w]=45}else{a[w]=32}while(1){g=c[y>>2]|0;c[y>>2]=g+ -1;if((g|0)<=0){break}g=a[w]|0;s=c[v>>2]|0;c[v>>2]=s+1;a[s]=g}if((c[p>>2]|0)==((c[j>>2]|0)-1|0)){break}if((((c[p>>2]|0)+1|0)%(c[n>>2]|0)|0|0)==0){g=Z(c[q>>2]|0,c[j>>2]|0)|0;c[z>>2]=c[(c[(c[k>>2]|0)+16>>2]|0)+(g+(c[p>>2]|0)<<2)>>2];g=Z(c[q>>2]|0,c[j>>2]|0)|0;c[A>>2]=c[(c[(c[k>>2]|0)+16>>2]|0)+(g+(c[p>>2]|0)+1<<2)>>2];g=Z((c[q>>2]|0)+1|0,c[j>>2]|0)|0;c[B>>2]=c[(c[(c[k>>2]|0)+16>>2]|0)+(g+(c[p>>2]|0)<<2)>>2];g=Z((c[q>>2]|0)+1|0,c[j>>2]|0)|0;c[C>>2]=c[(c[(c[k>>2]|0)+16>>2]|0)+(g+(c[p>>2]|0)+1<<2)>>2];if(((c[z>>2]|0)==(c[A>>2]|0)?(c[A>>2]|0)==(c[B>>2]|0):0)?(c[B>>2]|0)==(c[C>>2]|0):0){a[w]=32}else{F=48}do{if((F|0)==48){F=0;if((c[z>>2]|0)==(c[B>>2]|0)?(c[A>>2]|0)==(c[C>>2]|0):0){a[w]=124;break}if((c[z>>2]|0)==(c[A>>2]|0)?(c[B>>2]|0)==(c[C>>2]|0):0){a[w]=45;break}a[w]=43}}while(0);g=a[w]|0;s=c[v>>2]|0;c[v>>2]=s+1;a[s]=g}c[p>>2]=(c[p>>2]|0)+1}g=c[v>>2]|0;c[v>>2]=g+1;a[g]=10}}while(0);c[q>>2]=(c[q>>2]|0)+1}if(((c[v>>2]|0)-(c[u>>2]|0)|0)==(c[r>>2]|0)){a[c[v>>2]|0]=0;i=h;return c[u>>2]|0}else{Ba(4920,4528,4417,4944)}return 0}function ef(b,e,f,g,h,j,k){b=b|0;e=e|0;f=f|0;g=g|0;h=h|0;j=j|0;k=k|0;var l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0,L=0,M=0,N=0,O=0,P=0,Q=0,R=0,S=0,T=0,U=0,V=0,W=0,X=0,Y=0,_=0,$=0,aa=0,ba=0,ca=0,da=0,ea=0,fa=0,ga=0,ha=0,ia=0,ja=0,ka=0,la=0,ma=0,na=0,oa=0,pa=0,qa=0,ra=0;l=i;i=i+192|0;m=l+176|0;n=l+172|0;o=l+168|0;p=l+164|0;q=l+160|0;r=l+156|0;s=l+152|0;t=l+148|0;u=l+144|0;v=l+140|0;w=l+136|0;x=l+132|0;y=l+128|0;z=l+124|0;A=l+120|0;B=l+116|0;C=l+112|0;D=l+108|0;E=l+104|0;F=l+100|0;G=l+96|0;H=l+92|0;I=l+88|0;J=l+84|0;K=l+80|0;L=l+76|0;M=l+72|0;N=l+68|0;O=l+64|0;P=l+60|0;Q=l+56|0;R=l+52|0;S=l+48|0;T=l+44|0;U=l+40|0;V=l+36|0;W=l+32|0;X=l+28|0;Y=l+24|0;_=l+20|0;$=l+16|0;aa=l+12|0;ba=l+8|0;ca=l+4|0;da=l;c[m>>2]=b;c[n>>2]=e;c[o>>2]=f;c[p>>2]=g;c[q>>2]=h;c[r>>2]=j;c[s>>2]=k;c[B>>2]=0;c[C>>2]=0;c[t>>2]=sd(60)|0;c[c[t>>2]>>2]=c[m>>2];c[(c[t>>2]|0)+4>>2]=c[n>>2];if((c[o>>2]|0)!=0){k=gf(c[o>>2]|0)|0;c[(c[t>>2]|0)+8>>2]=k;k=Z(c[m>>2]|0,c[m>>2]|0)|0;j=hf(c[(c[o>>2]|0)+4>>2]|0,c[(c[o>>2]|0)+8>>2]|0,k,c[m>>2]|0,Z(c[m>>2]|0,c[m>>2]|0)|0)|0;c[(c[t>>2]|0)+12>>2]=j;j=sd(Z(c[m>>2]|0,c[m>>2]|0)|0)|0;c[(c[t>>2]|0)+28>>2]=j}else{c[(c[t>>2]|0)+12>>2]=0;c[(c[t>>2]|0)+8>>2]=0;c[(c[t>>2]|0)+28>>2]=0}j=Z(c[m>>2]|0,c[m>>2]|0)|0;k=sd(Z(j,c[m>>2]|0)|0)|0;c[(c[t>>2]|0)+16>>2]=k;c[(c[t>>2]|0)+20>>2]=c[q>>2];do{if((c[r>>2]|0)!=0){if((c[o>>2]|0)==0){Ba(5112,4528,1719,5120)}c[D>>2]=c[(c[o>>2]|0)+32>>2];k=sd(Z(c[m>>2]|0,c[m>>2]|0)|0)|0;c[(c[t>>2]|0)+24>>2]=k;c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[D>>2]|0)){ea=17;break}c[z>>2]=0;while(1){if((c[z>>2]|0)>=(c[(c[(c[o>>2]|0)+24>>2]|0)+(c[y>>2]<<2)>>2]|0)){break}if((d[(c[r>>2]|0)+(c[(c[(c[(c[o>>2]|0)+20>>2]|0)+(c[y>>2]<<2)>>2]|0)+(c[z>>2]<<2)>>2]|0)|0]|0)!=0){a[(c[(c[t>>2]|0)+24>>2]|0)+(c[y>>2]|0)|0]=a[(c[r>>2]|0)+(c[(c[(c[(c[o>>2]|0)+20>>2]|0)+(c[y>>2]<<2)>>2]|0)+(c[z>>2]<<2)>>2]|0)|0]|0}c[z>>2]=(c[z>>2]|0)+1}if((d[(c[(c[t>>2]|0)+24>>2]|0)+(c[y>>2]|0)|0]|0)<=0){ea=15;break}c[y>>2]=(c[y>>2]|0)+1}if((ea|0)==15){Ba(5128,4528,1730,5120)}else if((ea|0)==17){k=Z(c[m>>2]|0,c[m>>2]|0)|0;cg((c[(c[t>>2]|0)+24>>2]|0)+(c[D>>2]|0)|0,0,k-(c[D>>2]|0)|0)|0;break}}else{c[(c[t>>2]|0)+24>>2]=0}}while(0);D=Z(c[m>>2]|0,c[m>>2]|0)|0;cg(c[(c[t>>2]|0)+16>>2]|0,1,Z(D,c[m>>2]|0)|0)|0;D=sd(Z(c[m>>2]|0,c[m>>2]|0)|0)|0;c[(c[t>>2]|0)+32>>2]=D;D=sd(Z(c[m>>2]|0,c[m>>2]|0)|0)|0;c[(c[t>>2]|0)+36>>2]=D;D=sd(Z(c[m>>2]|0,c[m>>2]|0)|0)|0;c[(c[t>>2]|0)+40>>2]=D;cg(c[(c[t>>2]|0)+32>>2]|0,0,Z(c[m>>2]|0,c[m>>2]|0)|0)|0;cg(c[(c[t>>2]|0)+36>>2]|0,0,Z(c[m>>2]|0,c[m>>2]|0)|0)|0;cg(c[(c[t>>2]|0)+40>>2]|0,0,Z(c[m>>2]|0,c[m>>2]|0)|0)|0;if((c[p>>2]|0)!=0){D=sd(c[m>>2]<<1)|0;c[(c[t>>2]|0)+44>>2]=D;cg(c[(c[t>>2]|0)+44>>2]|0,0,c[m>>2]<<1|0)|0}else{c[(c[t>>2]|0)+44>>2]=0}c[(c[t>>2]|0)+52>>2]=((c[m>>2]|0)*3|0)+((c[p>>2]|0)!=0?2:0);D=sd((Z(c[m>>2]|0,c[(c[t>>2]|0)+52>>2]|0)|0)<<2)|0;c[(c[t>>2]|0)+48>>2]=D;D=sd((Z(c[m>>2]|0,c[m>>2]|0)|0)*3<<2)|0;c[(c[t>>2]|0)+56>>2]=D;c[z>>2]=0;while(1){if((c[z>>2]|0)>=(c[m>>2]|0)){break}c[y>>2]=0;while(1){fa=c[z>>2]|0;if((c[y>>2]|0)>=(c[m>>2]|0)){break}D=Z(fa,c[m>>2]|0)|0;c[v>>2]=D+(c[y>>2]|0);D=Z(c[y>>2]|0,c[m>>2]|0)|0;c[w>>2]=D+(c[z>>2]|0);c[x>>2]=c[(c[(c[(c[(c[t>>2]|0)+4>>2]|0)+20>>2]|0)+(c[z>>2]<<2)>>2]|0)+(c[y>>2]<<2)>>2];D=(Z(c[m>>2]|0,c[z>>2]|0)|0)*3|0;c[(c[(c[t>>2]|0)+48>>2]|0)+(D+(c[y>>2]|0)<<2)>>2]=c[v>>2];D=(Z(c[m>>2]|0,c[z>>2]|0)|0)*3|0;c[(c[(c[t>>2]|0)+48>>2]|0)+(D+(c[m>>2]|0)+(c[y>>2]|0)<<2)>>2]=c[w>>2];D=(Z(c[m>>2]|0,c[z>>2]|0)|0)*3|0;c[(c[(c[t>>2]|0)+48>>2]|0)+(D+(c[m>>2]<<1)+(c[y>>2]|0)<<2)>>2]=c[x>>2];D=(c[(c[t>>2]|0)+48>>2]|0)+((Z(c[m>>2]|0,c[z>>2]|0)|0)*3<<2)|0;c[(c[(c[t>>2]|0)+56>>2]|0)+((c[v>>2]|0)*3<<2)>>2]=D;D=(c[(c[t>>2]|0)+48>>2]|0)+((Z(c[m>>2]|0,c[z>>2]|0)|0)*3<<2)|0;c[(c[(c[t>>2]|0)+56>>2]|0)+(((c[w>>2]|0)*3|0)+1<<2)>>2]=D+(c[m>>2]<<2);D=(c[(c[t>>2]|0)+48>>2]|0)+((Z(c[m>>2]|0,c[z>>2]|0)|0)*3<<2)|0;c[(c[(c[t>>2]|0)+56>>2]|0)+(((c[x>>2]|0)*3|0)+2<<2)>>2]=D+(c[m>>2]<<1<<2);c[y>>2]=(c[y>>2]|0)+1}c[z>>2]=fa+1}c[u>>2]=jf(c[t>>2]|0)|0;c[v>>2]=0;a:while(1){if((c[v>>2]|0)>=(c[m>>2]|0)){ea=38;break}c[w>>2]=0;while(1){if((c[w>>2]|0)>=(c[m>>2]|0)){break}fa=Z(c[w>>2]|0,c[m>>2]|0)|0;c[E>>2]=d[(c[q>>2]|0)+(fa+(c[v>>2]|0))|0]|0;if((c[E>>2]|0)!=0){fa=Z(c[w>>2]|0,c[c[t>>2]>>2]|0)|0;D=Z(fa+(c[v>>2]|0)|0,c[c[t>>2]>>2]|0)|0;if((a[(c[(c[t>>2]|0)+16>>2]|0)+(D+(c[E>>2]|0)-1)|0]|0)==0){ea=34;break a}D=Z(c[w>>2]|0,c[m>>2]|0)|0;kf(c[t>>2]|0,c[v>>2]|0,c[w>>2]|0,d[(c[q>>2]|0)+(D+(c[v>>2]|0))|0]|0)}c[w>>2]=(c[w>>2]|0)+1}c[v>>2]=(c[v>>2]|0)+1}b:do{if((ea|0)==34){c[B>>2]=7}else if((ea|0)==38){c:while(1){ea=0;c[x>>2]=0;d:while(1){if((c[x>>2]|0)>=(c[m>>2]|0)){break}c[z>>2]=1;while(1){ga=c[x>>2]|0;if((c[z>>2]|0)>(c[m>>2]|0)){break}E=Z(ga,c[m>>2]|0)|0;if((a[(c[(c[t>>2]|0)+40>>2]|0)+(E+(c[z>>2]|0)-1)|0]|0)==0){c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[m>>2]|0)){break}E=Z(c[(c[(c[(c[(c[t>>2]|0)+4>>2]|0)+20>>2]|0)+(c[x>>2]<<2)>>2]|0)+(c[y>>2]<<2)>>2]|0,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(c[y>>2]<<2)>>2]=E+(c[z>>2]|0)-1;c[y>>2]=(c[y>>2]|0)+1}c[A>>2]=lf(c[t>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0;if((c[A>>2]|0)<0){ea=47;break c}if((c[A>>2]|0)>0){ea=49;break d}}c[z>>2]=(c[z>>2]|0)+1}c[x>>2]=ga+1}if((ea|0)==49){ea=0;c[B>>2]=(c[B>>2]|0)>0?c[B>>2]|0:0;ea=38;continue}if((c[(c[t>>2]|0)+24>>2]|0)!=0){c[F>>2]=0;c[x>>2]=0;while(1){if((c[x>>2]|0)>=(c[(c[(c[t>>2]|0)+8>>2]|0)+32>>2]|0)){break}c[y>>2]=(c[(c[(c[(c[t>>2]|0)+8>>2]|0)+24>>2]|0)+(c[x>>2]<<2)>>2]|0)-1;while(1){if((c[y>>2]|0)<0){break}c[G>>2]=c[(c[(c[(c[(c[t>>2]|0)+8>>2]|0)+20>>2]|0)+(c[x>>2]<<2)>>2]|0)+(c[y>>2]<<2)>>2];c[H>>2]=d[(c[(c[t>>2]|0)+20>>2]|0)+(c[G>>2]|0)|0]|0;e:do{if((c[H>>2]|0)!=0){mf(c[(c[t>>2]|0)+8>>2]|0,c[x>>2]|0,c[G>>2]|0);if((c[H>>2]|0)>(d[(c[(c[t>>2]|0)+24>>2]|0)+(c[x>>2]|0)|0]|0)){ea=59;break c}E=(c[(c[t>>2]|0)+24>>2]|0)+(c[x>>2]|0)|0;a[E]=(d[E]|0)-(c[H>>2]|0);c[z>>2]=0;while(1){if((c[z>>2]|0)>=(c[(c[(c[(c[t>>2]|0)+8>>2]|0)+24>>2]|0)+(c[x>>2]<<2)>>2]|0)){break e}E=Z(c[(c[(c[(c[(c[t>>2]|0)+8>>2]|0)+20>>2]|0)+(c[x>>2]<<2)>>2]|0)+(c[z>>2]<<2)>>2]|0,c[c[t>>2]>>2]|0)|0;a[(c[(c[t>>2]|0)+16>>2]|0)+(E+(c[H>>2]|0)-1)|0]=0;c[z>>2]=(c[z>>2]|0)+1}}}while(0);c[y>>2]=(c[y>>2]|0)+ -1}c[x>>2]=(c[x>>2]|0)+1}c[x>>2]=0;while(1){if((c[x>>2]|0)>=(c[(c[(c[t>>2]|0)+8>>2]|0)+32>>2]|0)){break}c[I>>2]=c[(c[(c[(c[t>>2]|0)+8>>2]|0)+24>>2]|0)+(c[x>>2]<<2)>>2];if((c[I>>2]|0)==1){c[J>>2]=d[(c[(c[t>>2]|0)+24>>2]|0)+(c[x>>2]|0)|0]|0;if((c[J>>2]|0)<1){ea=70;break c}if((c[J>>2]|0)>(c[m>>2]|0)){ea=70;break c}c[v>>2]=(c[c[(c[(c[(c[t>>2]|0)+8>>2]|0)+20>>2]|0)+(c[x>>2]<<2)>>2]>>2]|0)%(c[m>>2]|0)|0;c[w>>2]=(c[c[(c[(c[(c[t>>2]|0)+8>>2]|0)+20>>2]|0)+(c[x>>2]<<2)>>2]>>2]|0)/(c[m>>2]|0)|0;E=Z(c[w>>2]|0,c[c[t>>2]>>2]|0)|0;D=Z(E+(c[v>>2]|0)|0,c[c[t>>2]>>2]|0)|0;if((a[(c[(c[t>>2]|0)+16>>2]|0)+(D+(c[J>>2]|0)-1)|0]|0)==0){ea=72;break c}kf(c[t>>2]|0,c[v>>2]|0,c[w>>2]|0,c[J>>2]|0);c[F>>2]=1}c[x>>2]=(c[x>>2]|0)+1}if((c[F>>2]|0)!=0){c[C>>2]=(c[C>>2]|0)>0?c[C>>2]|0:0;ea=38;continue}}if((c[(c[s>>2]|0)+4>>2]|0)>=3?(c[(c[t>>2]|0)+24>>2]|0)!=0:0){c[K>>2]=0;c[(c[(c[t>>2]|0)+12>>2]|0)+32>>2]=0;c[y>>2]=0;while(1){if((c[y>>2]|0)>=3){break}c[z>>2]=0;while(1){if((c[z>>2]|0)>=(c[m>>2]|0)){break}D=(c[(c[t>>2]|0)+48>>2]|0)+((Z(c[m>>2]|0,c[z>>2]|0)|0)*3<<2)|0;c[L>>2]=D+((Z(c[y>>2]|0,c[m>>2]|0)|0)<<2);c[M>>2]=(Z(c[m>>2]|0,(c[m>>2]|0)+1|0)|0)/2|0;c[N>>2]=c[m>>2];c[P>>2]=c[(c[(c[t>>2]|0)+12>>2]|0)+32>>2];c[Q>>2]=c[(c[(c[(c[t>>2]|0)+12>>2]|0)+20>>2]|0)+(c[P>>2]<<2)>>2];eg(c[Q>>2]|0,c[L>>2]|0,c[m>>2]<<2|0)|0;c[N>>2]=nf(c[t>>2]|0,c[Q>>2]|0,c[N>>2]|0,O)|0;c[M>>2]=(c[M>>2]|0)-(c[O>>2]|0);do{if(!((c[N>>2]|0)==(c[m>>2]|0)|(c[N>>2]|0)==0)){if((c[c[s>>2]>>2]|0)>=5?(c[M>>2]|0)<=0:0){ea=86;break c}if((c[M>>2]|0)<=0){ea=88;break c}if((c[N>>2]|0)==1){if((c[M>>2]|0)>(c[m>>2]|0)){ea=91;break c}c[v>>2]=(c[c[Q>>2]>>2]|0)%(c[m>>2]|0)|0;c[w>>2]=(c[c[Q>>2]>>2]|0)/(c[m>>2]|0)|0;D=Z(c[w>>2]|0,c[c[t>>2]>>2]|0)|0;E=Z(D+(c[v>>2]|0)|0,c[c[t>>2]>>2]|0)|0;if((a[(c[(c[t>>2]|0)+16>>2]|0)+(E+(c[M>>2]|0)-1)|0]|0)==0){ea=93;break c}kf(c[t>>2]|0,c[v>>2]|0,c[w>>2]|0,c[M>>2]|0);c[K>>2]=1}c[x>>2]=c[(c[(c[(c[t>>2]|0)+8>>2]|0)+16>>2]|0)+(c[c[Q>>2]>>2]<<2)>>2];c[v>>2]=1;while(1){if((c[v>>2]|0)>=(c[N>>2]|0)){break}if((c[(c[(c[(c[t>>2]|0)+8>>2]|0)+16>>2]|0)+(c[(c[Q>>2]|0)+(c[v>>2]<<2)>>2]<<2)>>2]|0)!=(c[x>>2]|0)){break}c[v>>2]=(c[v>>2]|0)+1}if((c[v>>2]|0)!=(c[N>>2]|0)){c[(c[(c[(c[t>>2]|0)+12>>2]|0)+24>>2]|0)+(c[P>>2]<<2)>>2]=c[N>>2];E=(c[(c[t>>2]|0)+12>>2]|0)+32|0;c[E>>2]=(c[E>>2]|0)+1;a[(c[(c[t>>2]|0)+28>>2]|0)+(c[P>>2]|0)|0]=c[M>>2];break}if((c[(c[(c[(c[t>>2]|0)+8>>2]|0)+24>>2]|0)+(c[x>>2]<<2)>>2]|0)<=(c[N>>2]|0)){ea=101;break c}of(c[(c[t>>2]|0)+8>>2]|0,c[Q>>2]|0,c[N>>2]|0);if((c[(c[(c[(c[t>>2]|0)+8>>2]|0)+24>>2]|0)+((c[(c[(c[t>>2]|0)+8>>2]|0)+32>>2]|0)-1<<2)>>2]|0)!=(c[N>>2]|0)){ea=103;break c}a[(c[(c[t>>2]|0)+24>>2]|0)+((c[(c[(c[t>>2]|0)+8>>2]|0)+32>>2]|0)-1)|0]=c[M>>2];E=(c[(c[t>>2]|0)+24>>2]|0)+(c[x>>2]|0)|0;a[E]=(d[E]|0)-(c[M>>2]|0)}}while(0);c[z>>2]=(c[z>>2]|0)+1}c[y>>2]=(c[y>>2]|0)+1}if((c[K>>2]|0)!=0){c[C>>2]=(c[C>>2]|0)>3?c[C>>2]|0:3;ea=38;continue}}if((c[(c[s>>2]|0)+4>>2]|0)>=1?(c[(c[t>>2]|0)+24>>2]|0)!=0:0){c[R>>2]=0;c[x>>2]=0;while(1){if((c[x>>2]|0)>=(c[(c[(c[t>>2]|0)+8>>2]|0)+32>>2]|0)){break}c[S>>2]=pf(c[t>>2]|0,c[(c[t>>2]|0)+8>>2]|0,c[(c[t>>2]|0)+24>>2]|0,c[x>>2]|0)|0;if((c[S>>2]|0)<0){ea=115;break c}if((c[S>>2]|0)>0){c[R>>2]=1}c[x>>2]=(c[x>>2]|0)+1}c[x>>2]=0;while(1){if((c[x>>2]|0)>=(c[(c[(c[t>>2]|0)+12>>2]|0)+32>>2]|0)){break}c[T>>2]=pf(c[t>>2]|0,c[(c[t>>2]|0)+12>>2]|0,c[(c[t>>2]|0)+28>>2]|0,c[x>>2]|0)|0;if((c[T>>2]|0)<0){ea=122;break c}if((c[T>>2]|0)>0){c[R>>2]=1}c[x>>2]=(c[x>>2]|0)+1}if((c[R>>2]|0)!=0){c[C>>2]=(c[C>>2]|0)>1?c[C>>2]|0:1;ea=38;continue}}if((c[(c[s>>2]|0)+4>>2]|0)>=2?(c[(c[t>>2]|0)+24>>2]|0)!=0:0){c[U>>2]=0;c[x>>2]=0;while(1){if((c[x>>2]|0)>=(c[(c[(c[t>>2]|0)+8>>2]|0)+32>>2]|0)){break}c[V>>2]=qf(c[t>>2]|0,c[x>>2]|0,c[(c[t>>2]|0)+8>>2]|0,d[(c[(c[t>>2]|0)+24>>2]|0)+(c[x>>2]|0)|0]|0,1)|0;if((c[V>>2]|0)<=0){if((c[V>>2]|0)<0){ea=135;break c}}else{c[U>>2]=1;c[C>>2]=(c[C>>2]|0)>2?c[C>>2]|0:2}c[x>>2]=(c[x>>2]|0)+1}c[x>>2]=0;while(1){if((c[x>>2]|0)>=(c[(c[(c[t>>2]|0)+12>>2]|0)+32>>2]|0)){break}c[W>>2]=qf(c[t>>2]|0,c[x>>2]|0,c[(c[t>>2]|0)+12>>2]|0,d[(c[(c[t>>2]|0)+28>>2]|0)+(c[x>>2]|0)|0]|0,0)|0;if((c[W>>2]|0)<=0){if((c[W>>2]|0)<0){ea=142;break c}}else{c[U>>2]=1;c[C>>2]=(c[C>>2]|0)>2?c[C>>2]|0:2}c[x>>2]=(c[x>>2]|0)+1}if((c[U>>2]|0)!=0){ea=38;continue}}if((c[c[s>>2]>>2]|0)<=0){ea=350;break}c[w>>2]=0;f:while(1){if((c[w>>2]|0)>=(c[m>>2]|0)){break}c[z>>2]=1;while(1){ha=c[w>>2]|0;if((c[z>>2]|0)>(c[m>>2]|0)){break}E=Z(ha,c[m>>2]|0)|0;if((a[(c[(c[t>>2]|0)+32>>2]|0)+(E+(c[z>>2]|0)-1)|0]|0)==0){c[v>>2]=0;while(1){if((c[v>>2]|0)>=(c[m>>2]|0)){break}E=Z(c[w>>2]|0,c[c[t>>2]>>2]|0)|0;D=Z(E+(c[v>>2]|0)|0,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(c[v>>2]<<2)>>2]=D+(c[z>>2]|0)-1;c[v>>2]=(c[v>>2]|0)+1}c[A>>2]=lf(c[t>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0;if((c[A>>2]|0)<0){ea=155;break c}if((c[A>>2]|0)>0){ea=157;break f}}c[z>>2]=(c[z>>2]|0)+1}c[w>>2]=ha+1}if((ea|0)==157){ea=0;c[B>>2]=(c[B>>2]|0)>1?c[B>>2]|0:1;ea=38;continue}c[v>>2]=0;g:while(1){if((c[v>>2]|0)>=(c[m>>2]|0)){break}c[z>>2]=1;while(1){ia=c[v>>2]|0;if((c[z>>2]|0)>(c[m>>2]|0)){break}D=Z(ia,c[m>>2]|0)|0;if((a[(c[(c[t>>2]|0)+36>>2]|0)+(D+(c[z>>2]|0)-1)|0]|0)==0){c[w>>2]=0;while(1){if((c[w>>2]|0)>=(c[m>>2]|0)){break}D=Z(c[w>>2]|0,c[c[t>>2]>>2]|0)|0;E=Z(D+(c[v>>2]|0)|0,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(c[w>>2]<<2)>>2]=E+(c[z>>2]|0)-1;c[w>>2]=(c[w>>2]|0)+1}c[A>>2]=lf(c[t>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0;if((c[A>>2]|0)<0){ea=169;break c}if((c[A>>2]|0)>0){ea=171;break g}}c[z>>2]=(c[z>>2]|0)+1}c[v>>2]=ia+1}if((ea|0)==171){ea=0;c[B>>2]=(c[B>>2]|0)>1?c[B>>2]|0:1;ea=38;continue}h:do{if((c[(c[t>>2]|0)+44>>2]|0)!=0){c[z>>2]=1;while(1){if((c[z>>2]|0)>(c[m>>2]|0)){break}if((a[(c[(c[t>>2]|0)+44>>2]|0)+((c[z>>2]|0)-1)|0]|0)==0){c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[m>>2]|0)){break}E=Z(c[y>>2]|0,(c[m>>2]|0)+1|0)|0;D=Z(E,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(c[y>>2]<<2)>>2]=D+(c[z>>2]|0)-1;c[y>>2]=(c[y>>2]|0)+1}c[A>>2]=lf(c[t>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0;if((c[A>>2]|0)<0){ea=182;break c}if((c[A>>2]|0)>0){ea=184;break}}c[z>>2]=(c[z>>2]|0)+1}if((ea|0)==184){ea=0;c[B>>2]=(c[B>>2]|0)>1?c[B>>2]|0:1;ea=38;continue c}c[z>>2]=1;while(1){if((c[z>>2]|0)>(c[m>>2]|0)){break h}if((a[(c[(c[t>>2]|0)+44>>2]|0)+((c[m>>2]|0)+(c[z>>2]|0)-1)|0]|0)==0){c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[m>>2]|0)){break}D=Z((c[y>>2]|0)+1|0,(c[m>>2]|0)-1|0)|0;E=Z(D,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(c[y>>2]<<2)>>2]=E+(c[z>>2]|0)-1;c[y>>2]=(c[y>>2]|0)+1}c[A>>2]=lf(c[t>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0;if((c[A>>2]|0)<0){ea=193;break c}if((c[A>>2]|0)>0){break}}c[z>>2]=(c[z>>2]|0)+1}c[B>>2]=(c[B>>2]|0)>1?c[B>>2]|0:1;ea=38;continue c}}while(0);c[v>>2]=0;i:while(1){if((c[v>>2]|0)>=(c[m>>2]|0)){break}c[w>>2]=0;while(1){if((c[w>>2]|0)>=(c[m>>2]|0)){break}E=Z(c[w>>2]|0,c[m>>2]|0)|0;if((a[(c[(c[t>>2]|0)+20>>2]|0)+(E+(c[v>>2]|0))|0]|0)==0){c[z>>2]=1;while(1){if((c[z>>2]|0)>(c[m>>2]|0)){break}E=Z(c[w>>2]|0,c[c[t>>2]>>2]|0)|0;D=Z(E+(c[v>>2]|0)|0,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+((c[z>>2]|0)-1<<2)>>2]=D+(c[z>>2]|0)-1;c[z>>2]=(c[z>>2]|0)+1}c[A>>2]=lf(c[t>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0;if((c[A>>2]|0)<0){ea=206;break c}if((c[A>>2]|0)>0){ea=208;break i}}c[w>>2]=(c[w>>2]|0)+1}c[v>>2]=(c[v>>2]|0)+1}if((ea|0)==208){ea=0;c[B>>2]=(c[B>>2]|0)>1?c[B>>2]|0:1;ea=38;continue}if((c[c[s>>2]>>2]|0)<=1){ea=350;break}c[w>>2]=0;j:while(1){if((c[w>>2]|0)>=(c[m>>2]|0)){break}c[x>>2]=0;while(1){if((c[x>>2]|0)>=(c[m>>2]|0)){break}c[z>>2]=1;while(1){if((c[z>>2]|0)>(c[m>>2]|0)){break}D=Z(c[w>>2]|0,c[m>>2]|0)|0;if((d[(c[(c[t>>2]|0)+32>>2]|0)+(D+(c[z>>2]|0)-1)|0]|0)==0?(D=Z(c[x>>2]|0,c[m>>2]|0)|0,(d[(c[(c[t>>2]|0)+40>>2]|0)+(D+(c[z>>2]|0)-1)|0]|0)==0):0){c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[m>>2]|0)){break}D=Z(c[w>>2]|0,c[c[t>>2]>>2]|0)|0;E=Z(D+(c[y>>2]|0)|0,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(c[y>>2]<<2)>>2]=E+(c[z>>2]|0)-1;E=Z(c[(c[(c[(c[(c[t>>2]|0)+4>>2]|0)+20>>2]|0)+(c[x>>2]<<2)>>2]|0)+(c[y>>2]<<2)>>2]|0,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+28>>2]|0)+(c[y>>2]<<2)>>2]=E+(c[z>>2]|0)-1;c[y>>2]=(c[y>>2]|0)+1}if((rf(c[t>>2]|0,c[(c[u>>2]|0)+24>>2]|0,c[(c[u>>2]|0)+28>>2]|0)|0)!=0){ea=225;break j}if((rf(c[t>>2]|0,c[(c[u>>2]|0)+28>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0)!=0){ea=225;break j}}c[z>>2]=(c[z>>2]|0)+1}c[x>>2]=(c[x>>2]|0)+1}c[w>>2]=(c[w>>2]|0)+1}if((ea|0)==225){ea=0;c[B>>2]=(c[B>>2]|0)>2?c[B>>2]|0:2;ea=38;continue}c[v>>2]=0;k:while(1){if((c[v>>2]|0)>=(c[m>>2]|0)){break}c[x>>2]=0;while(1){if((c[x>>2]|0)>=(c[m>>2]|0)){break}c[z>>2]=1;while(1){if((c[z>>2]|0)>(c[m>>2]|0)){break}E=Z(c[v>>2]|0,c[m>>2]|0)|0;if((d[(c[(c[t>>2]|0)+36>>2]|0)+(E+(c[z>>2]|0)-1)|0]|0)==0?(E=Z(c[x>>2]|0,c[m>>2]|0)|0,(d[(c[(c[t>>2]|0)+40>>2]|0)+(E+(c[z>>2]|0)-1)|0]|0)==0):0){c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[m>>2]|0)){break}E=Z(c[y>>2]|0,c[c[t>>2]>>2]|0)|0;D=Z(E+(c[v>>2]|0)|0,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(c[y>>2]<<2)>>2]=D+(c[z>>2]|0)-1;D=Z(c[(c[(c[(c[(c[t>>2]|0)+4>>2]|0)+20>>2]|0)+(c[x>>2]<<2)>>2]|0)+(c[y>>2]<<2)>>2]|0,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+28>>2]|0)+(c[y>>2]<<2)>>2]=D+(c[z>>2]|0)-1;c[y>>2]=(c[y>>2]|0)+1}if((rf(c[t>>2]|0,c[(c[u>>2]|0)+24>>2]|0,c[(c[u>>2]|0)+28>>2]|0)|0)!=0){ea=242;break k}if((rf(c[t>>2]|0,c[(c[u>>2]|0)+28>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0)!=0){ea=242;break k}}c[z>>2]=(c[z>>2]|0)+1}c[x>>2]=(c[x>>2]|0)+1}c[v>>2]=(c[v>>2]|0)+1}if((ea|0)==242){ea=0;c[B>>2]=(c[B>>2]|0)>2?c[B>>2]|0:2;ea=38;continue}l:do{if((c[(c[t>>2]|0)+44>>2]|0)!=0){c[x>>2]=0;m:while(1){if((c[x>>2]|0)>=(c[m>>2]|0)){break}c[z>>2]=1;while(1){if((c[z>>2]|0)>(c[m>>2]|0)){break}if((d[(c[(c[t>>2]|0)+44>>2]|0)+((c[z>>2]|0)-1)|0]|0)==0?(D=Z(c[x>>2]|0,c[m>>2]|0)|0,(d[(c[(c[t>>2]|0)+40>>2]|0)+(D+(c[z>>2]|0)-1)|0]|0)==0):0){c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[m>>2]|0)){break}D=Z(c[y>>2]|0,(c[m>>2]|0)+1|0)|0;E=Z(D,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(c[y>>2]<<2)>>2]=E+(c[z>>2]|0)-1;E=Z(c[(c[(c[(c[(c[t>>2]|0)+4>>2]|0)+20>>2]|0)+(c[x>>2]<<2)>>2]|0)+(c[y>>2]<<2)>>2]|0,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+28>>2]|0)+(c[y>>2]<<2)>>2]=E+(c[z>>2]|0)-1;c[y>>2]=(c[y>>2]|0)+1}if((rf(c[t>>2]|0,c[(c[u>>2]|0)+24>>2]|0,c[(c[u>>2]|0)+28>>2]|0)|0)!=0){ea=258;break m}if((rf(c[t>>2]|0,c[(c[u>>2]|0)+28>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0)!=0){ea=258;break m}}c[z>>2]=(c[z>>2]|0)+1}c[x>>2]=(c[x>>2]|0)+1}if((ea|0)==258){ea=0;c[B>>2]=(c[B>>2]|0)>2?c[B>>2]|0:2;ea=38;continue c}c[x>>2]=0;n:while(1){if((c[x>>2]|0)>=(c[m>>2]|0)){break l}c[z>>2]=1;while(1){if((c[z>>2]|0)>(c[m>>2]|0)){break}if((d[(c[(c[t>>2]|0)+44>>2]|0)+((c[m>>2]|0)+(c[z>>2]|0)-1)|0]|0)==0?(E=Z(c[x>>2]|0,c[m>>2]|0)|0,(d[(c[(c[t>>2]|0)+40>>2]|0)+(E+(c[z>>2]|0)-1)|0]|0)==0):0){c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[m>>2]|0)){break}E=Z((c[y>>2]|0)+1|0,(c[m>>2]|0)-1|0)|0;D=Z(E,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(c[y>>2]<<2)>>2]=D+(c[z>>2]|0)-1;D=Z(c[(c[(c[(c[(c[t>>2]|0)+4>>2]|0)+20>>2]|0)+(c[x>>2]<<2)>>2]|0)+(c[y>>2]<<2)>>2]|0,c[c[t>>2]>>2]|0)|0;c[(c[(c[u>>2]|0)+28>>2]|0)+(c[y>>2]<<2)>>2]=D+(c[z>>2]|0)-1;c[y>>2]=(c[y>>2]|0)+1}if((rf(c[t>>2]|0,c[(c[u>>2]|0)+24>>2]|0,c[(c[u>>2]|0)+28>>2]|0)|0)!=0){break n}if((rf(c[t>>2]|0,c[(c[u>>2]|0)+28>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0)!=0){break n}}c[z>>2]=(c[z>>2]|0)+1}c[x>>2]=(c[x>>2]|0)+1}c[B>>2]=(c[B>>2]|0)>2?c[B>>2]|0:2;ea=38;continue c}}while(0);if((c[c[s>>2]>>2]|0)<=2){ea=350;break}c[x>>2]=0;while(1){if((c[x>>2]|0)>=(c[m>>2]|0)){break}c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[m>>2]|0)){break}c[z>>2]=1;while(1){ja=c[y>>2]|0;if((c[z>>2]|0)>(c[m>>2]|0)){break}D=Z(c[(c[(c[(c[(c[t>>2]|0)+4>>2]|0)+20>>2]|0)+(c[x>>2]<<2)>>2]|0)+(ja<<2)>>2]|0,c[c[t>>2]>>2]|0)|0;E=Z(c[y>>2]|0,c[m>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(E+(c[z>>2]|0)-1<<2)>>2]=D+(c[z>>2]|0)-1;c[z>>2]=(c[z>>2]|0)+1}c[y>>2]=ja+1}c[A>>2]=sf(c[t>>2]|0,c[u>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0;if((c[A>>2]|0)<0){ea=285;break c}if((c[A>>2]|0)>0){ea=287;break}c[x>>2]=(c[x>>2]|0)+1}if((ea|0)==287){ea=0;c[B>>2]=(c[B>>2]|0)>3?c[B>>2]|0:3;ea=38;continue}c[w>>2]=0;while(1){D=(c[w>>2]|0)<(c[m>>2]|0);c[v>>2]=0;if(!D){break}while(1){if((c[v>>2]|0)>=(c[m>>2]|0)){break}c[z>>2]=1;while(1){if((c[z>>2]|0)>(c[m>>2]|0)){break}D=Z(c[w>>2]|0,c[c[t>>2]>>2]|0)|0;E=Z(D+(c[v>>2]|0)|0,c[c[t>>2]>>2]|0)|0;D=Z(c[v>>2]|0,c[m>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(D+(c[z>>2]|0)-1<<2)>>2]=E+(c[z>>2]|0)-1;c[z>>2]=(c[z>>2]|0)+1}c[v>>2]=(c[v>>2]|0)+1}c[A>>2]=sf(c[t>>2]|0,c[u>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0;if((c[A>>2]|0)<0){ea=297;break c}if((c[A>>2]|0)>0){ea=299;break}c[w>>2]=(c[w>>2]|0)+1}if((ea|0)==299){ea=0;c[B>>2]=(c[B>>2]|0)>3?c[B>>2]|0:3;ea=38;continue}while(1){if((c[v>>2]|0)>=(c[m>>2]|0)){break}c[w>>2]=0;while(1){if((c[w>>2]|0)>=(c[m>>2]|0)){break}c[z>>2]=1;while(1){ka=c[w>>2]|0;if((c[z>>2]|0)>(c[m>>2]|0)){break}E=Z(ka,c[c[t>>2]>>2]|0)|0;D=Z(E+(c[v>>2]|0)|0,c[c[t>>2]>>2]|0)|0;E=Z(c[w>>2]|0,c[m>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(E+(c[z>>2]|0)-1<<2)>>2]=D+(c[z>>2]|0)-1;c[z>>2]=(c[z>>2]|0)+1}c[w>>2]=ka+1}c[A>>2]=sf(c[t>>2]|0,c[u>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0;if((c[A>>2]|0)<0){ea=309;break c}if((c[A>>2]|0)>0){ea=311;break}c[v>>2]=(c[v>>2]|0)+1}if((ea|0)==311){ea=0;c[B>>2]=(c[B>>2]|0)>3?c[B>>2]|0:3;ea=38;continue}if((c[(c[t>>2]|0)+44>>2]|0)!=0){c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[m>>2]|0)){break}c[z>>2]=1;while(1){la=c[y>>2]|0;if((c[z>>2]|0)>(c[m>>2]|0)){break}D=Z(la,(c[m>>2]|0)+1|0)|0;E=Z(D,c[c[t>>2]>>2]|0)|0;D=Z(c[y>>2]|0,c[m>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(D+(c[z>>2]|0)-1<<2)>>2]=E+(c[z>>2]|0)-1;c[z>>2]=(c[z>>2]|0)+1}c[y>>2]=la+1}c[A>>2]=sf(c[t>>2]|0,c[u>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0;if((c[A>>2]|0)<0){ea=321;break}if((c[A>>2]|0)>0){c[B>>2]=(c[B>>2]|0)>3?c[B>>2]|0:3;ea=38;continue}c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[m>>2]|0)){break}c[z>>2]=1;while(1){ma=(c[y>>2]|0)+1|0;if((c[z>>2]|0)>(c[m>>2]|0)){break}E=Z(ma,(c[m>>2]|0)-1|0)|0;D=Z(E,c[c[t>>2]>>2]|0)|0;E=Z(c[y>>2]|0,c[m>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(E+(c[z>>2]|0)-1<<2)>>2]=D+(c[z>>2]|0)-1;c[z>>2]=(c[z>>2]|0)+1}c[y>>2]=ma}c[A>>2]=sf(c[t>>2]|0,c[u>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0;if((c[A>>2]|0)<0){ea=331;break}if((c[A>>2]|0)>0){c[B>>2]=(c[B>>2]|0)>3?c[B>>2]|0:3;ea=38;continue}}if((c[c[s>>2]>>2]|0)<=3){ea=350;break}c[z>>2]=1;while(1){if((c[z>>2]|0)>(c[m>>2]|0)){break}c[w>>2]=0;while(1){if((c[w>>2]|0)>=(c[m>>2]|0)){break}c[v>>2]=0;while(1){na=c[w>>2]|0;if((c[v>>2]|0)>=(c[m>>2]|0)){break}D=Z(na,c[c[t>>2]>>2]|0)|0;E=Z(D+(c[v>>2]|0)|0,c[c[t>>2]>>2]|0)|0;D=Z(c[w>>2]|0,c[m>>2]|0)|0;c[(c[(c[u>>2]|0)+24>>2]|0)+(D+(c[v>>2]|0)<<2)>>2]=E+(c[z>>2]|0)-1;c[v>>2]=(c[v>>2]|0)+1}c[w>>2]=na+1}c[A>>2]=sf(c[t>>2]|0,c[u>>2]|0,c[(c[u>>2]|0)+24>>2]|0)|0;if((c[A>>2]|0)<0){ea=344;break c}if((c[A>>2]|0)>0){ea=346;break}c[z>>2]=(c[z>>2]|0)+1}if((ea|0)==346){ea=0;c[B>>2]=(c[B>>2]|0)>4?c[B>>2]|0:4;ea=38;continue}if((tf(c[t>>2]|0,c[u>>2]|0)|0)==0){ea=350;break}c[B>>2]=(c[B>>2]|0)>4?c[B>>2]|0:4;ea=38}switch(ea|0){case 47:{c[B>>2]=7;break b;break};case 59:{c[B>>2]=7;break b;break};case 70:{c[B>>2]=7;break b;break};case 72:{c[B>>2]=7;break b;break};case 86:{c[(c[s>>2]|0)+8>>2]=7;break b;break};case 88:{Ba(5152,4528,1927,5120);break};case 91:{c[B>>2]=7;break b;break};case 93:{c[B>>2]=7;break b;break};case 101:{Ba(5160,4528,1956,5120);break};case 103:{Ba(5208,4528,1958,5120);break};case 115:{c[B>>2]=7;break b;break};case 122:{c[B>>2]=7;break b;break};case 135:{c[B>>2]=7;break b;break};case 142:{c[B>>2]=7;break b;break};case 155:{c[B>>2]=7;break b;break};case 169:{c[B>>2]=7;break b;break};case 182:{c[B>>2]=7;break b;break};case 193:{c[B>>2]=7;break b;break};case 206:{c[B>>2]=7;break b;break};case 285:{c[B>>2]=7;break b;break};case 297:{c[B>>2]=7;break b;break};case 309:{c[B>>2]=7;break b;break};case 321:{c[B>>2]=7;break b;break};case 331:{c[B>>2]=7;break b;break};case 344:{c[B>>2]=7;break b;break};case 350:{if((c[c[s>>2]>>2]|0)<5){c[w>>2]=0;while(1){if((c[w>>2]|0)>=(c[m>>2]|0)){break b}c[v>>2]=0;while(1){oa=c[w>>2]|0;if((c[v>>2]|0)>=(c[m>>2]|0)){break}E=Z(oa,c[m>>2]|0)|0;if((a[(c[q>>2]|0)+(E+(c[v>>2]|0))|0]|0)==0){c[B>>2]=7}c[v>>2]=(c[v>>2]|0)+1}c[w>>2]=oa+1}}c[X>>2]=-1;c[Y>>2]=(c[m>>2]|0)+1;c[w>>2]=0;o:while(1){if((c[w>>2]|0)>=(c[m>>2]|0)){break}c[v>>2]=0;while(1){pa=c[w>>2]|0;if((c[v>>2]|0)>=(c[m>>2]|0)){break}E=Z(pa,c[m>>2]|0)|0;if((a[(c[q>>2]|0)+(E+(c[v>>2]|0))|0]|0)==0){c[_>>2]=0;c[z>>2]=1;while(1){if((c[z>>2]|0)>(c[m>>2]|0)){break}E=Z(c[w>>2]|0,c[c[t>>2]>>2]|0)|0;D=Z(E+(c[v>>2]|0)|0,c[c[t>>2]>>2]|0)|0;if((a[(c[(c[t>>2]|0)+16>>2]|0)+(D+(c[z>>2]|0)-1)|0]|0)!=0){c[_>>2]=(c[_>>2]|0)+1}c[z>>2]=(c[z>>2]|0)+1}if((c[_>>2]|0)<=1){ea=362;break o}if((c[_>>2]|0)<(c[Y>>2]|0)){c[Y>>2]=c[_>>2];D=Z(c[w>>2]|0,c[m>>2]|0)|0;c[X>>2]=D+(c[v>>2]|0)}}c[v>>2]=(c[v>>2]|0)+1}c[w>>2]=pa+1}if((ea|0)==362){Ba(5280,4528,2494,5120)}if(!((c[X>>2]|0)!=-1)){break b}c[B>>2]=7;c[w>>2]=(c[X>>2]|0)/(c[m>>2]|0)|0;c[v>>2]=(c[X>>2]|0)%(c[m>>2]|0)|0;c[ba>>2]=sd(c[m>>2]|0)|0;c[ca>>2]=sd(Z(c[m>>2]|0,c[m>>2]|0)|0)|0;c[da>>2]=sd(Z(c[m>>2]|0,c[m>>2]|0)|0)|0;eg(c[ca>>2]|0,c[q>>2]|0,Z(c[m>>2]|0,c[m>>2]|0)|0)|0;c[aa>>2]=0;c[z>>2]=1;while(1){if((c[z>>2]|0)>(c[m>>2]|0)){break}D=Z(c[w>>2]|0,c[c[t>>2]>>2]|0)|0;E=Z(D+(c[v>>2]|0)|0,c[c[t>>2]>>2]|0)|0;if((a[(c[(c[t>>2]|0)+16>>2]|0)+(E+(c[z>>2]|0)-1)|0]|0)!=0){E=c[z>>2]&255;D=c[aa>>2]|0;c[aa>>2]=D+1;a[(c[ba>>2]|0)+D|0]=E}c[z>>2]=(c[z>>2]|0)+1}c[$>>2]=0;while(1){if((c[$>>2]|0)>=(c[aa>>2]|0)){break}eg(c[da>>2]|0,c[ca>>2]|0,Z(c[m>>2]|0,c[m>>2]|0)|0)|0;E=Z(c[w>>2]|0,c[m>>2]|0)|0;a[(c[da>>2]|0)+(E+(c[v>>2]|0))|0]=a[(c[ba>>2]|0)+(c[$>>2]|0)|0]|0;ef(c[m>>2]|0,c[n>>2]|0,c[o>>2]|0,c[p>>2]|0,c[da>>2]|0,c[r>>2]|0,c[s>>2]|0);if((c[B>>2]|0)==7?(c[(c[s>>2]|0)+8>>2]|0)!=7:0){eg(c[q>>2]|0,c[da>>2]|0,Z(c[m>>2]|0,c[m>>2]|0)|0)|0}do{if((c[(c[s>>2]|0)+8>>2]|0)!=6){if((c[(c[s>>2]|0)+8>>2]|0)!=7){if((c[B>>2]|0)==7){c[B>>2]=5;break}else{c[B>>2]=6;break}}}else{c[B>>2]=6}}while(0);if((c[B>>2]|0)==6){break}c[$>>2]=(c[$>>2]|0)+1}td(c[da>>2]|0);td(c[ca>>2]|0);td(c[ba>>2]|0);break b;break}}}}while(0);c[(c[s>>2]|0)+8>>2]=c[B>>2];c[(c[s>>2]|0)+12>>2]=c[C>>2];td(c[(c[t>>2]|0)+56>>2]|0);td(c[(c[t>>2]|0)+48>>2]|0);td(c[(c[t>>2]|0)+16>>2]|0);td(c[(c[t>>2]|0)+32>>2]|0);td(c[(c[t>>2]|0)+36>>2]|0);td(c[(c[t>>2]|0)+40>>2]|0);if((c[(c[t>>2]|0)+8>>2]|0)!=0){uf(c[(c[t>>2]|0)+8>>2]|0);uf(c[(c[t>>2]|0)+12>>2]|0);td(c[(c[t>>2]|0)+28>>2]|0)}if((c[(c[t>>2]|0)+24>>2]|0)==0){qa=c[t>>2]|0;td(qa);ra=c[u>>2]|0;vf(ra);i=l;return}td(c[(c[t>>2]|0)+24>>2]|0);qa=c[t>>2]|0;td(qa);ra=c[u>>2]|0;vf(ra);i=l;return}function ff(b,e){b=b|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;f=i;i=i+48|0;g=f;h=f+32|0;j=f+28|0;k=f+24|0;l=f+20|0;m=f+16|0;n=f+12|0;o=f+8|0;c[h>>2]=b;c[j>>2]=e;c[l>>2]=0;c[k>>2]=1;while(1){p=c[h>>2]|0;if((c[k>>2]|0)>(c[h>>2]|0)){break}if((p-(c[k>>2]|0)+1|0)>0){q=(c[h>>2]|0)-(c[k>>2]|0)+1|0}else{q=0}c[l>>2]=(c[l>>2]|0)+q;c[k>>2]=(c[k>>2]|0)*10}c[l>>2]=(c[l>>2]|0)+p;c[l>>2]=Z(c[l>>2]|0,c[h>>2]|0)|0;c[l>>2]=(c[l>>2]|0)+1;c[m>>2]=sd(c[l>>2]|0)|0;c[n>>2]=c[m>>2];p=c[n>>2]|0;c[n>>2]=p+1;a[p]=83;c[o>>2]=4848;c[k>>2]=0;while(1){p=(c[k>>2]|0)<(Z(c[h>>2]|0,c[h>>2]|0)|0);r=c[n>>2]|0;if(!p){break}p=d[(c[j>>2]|0)+(c[k>>2]|0)|0]|0;c[g>>2]=c[o>>2];c[g+4>>2]=p;p=ab(r|0,5056,g|0)|0;c[n>>2]=(c[n>>2]|0)+p;c[o>>2]=5064;c[k>>2]=(c[k>>2]|0)+1}c[n>>2]=r+1;a[r]=0;if(((c[n>>2]|0)-(c[m>>2]|0)|0)==(c[l>>2]|0)){i=f;return c[m>>2]|0}else{Ba(5072,4528,3157,5088)}return 0}function gf(a){a=a|0;var b=0,d=0,e=0,f=0,g=0;b=i;i=i+16|0;d=b+8|0;e=b+4|0;f=b;c[d>>2]=a;c[e>>2]=hf(c[(c[d>>2]|0)+4>>2]|0,c[(c[d>>2]|0)+8>>2]|0,c[(c[d>>2]|0)+12>>2]|0,c[(c[d>>2]|0)+36>>2]|0,c[(c[d>>2]|0)+32>>2]|0)|0;eg(c[(c[e>>2]|0)+24>>2]|0,c[(c[d>>2]|0)+24>>2]|0,c[(c[d>>2]|0)+32>>2]<<2|0)|0;eg(c[(c[e>>2]|0)+16>>2]|0,c[(c[d>>2]|0)+16>>2]|0,c[(c[d>>2]|0)+12>>2]<<2|0)|0;eg(c[(c[e>>2]|0)+28>>2]|0,c[(c[d>>2]|0)+28>>2]|0,(Z(c[(c[d>>2]|0)+32>>2]|0,c[(c[d>>2]|0)+36>>2]|0)|0)<<2|0)|0;c[f>>2]=0;while(1){g=c[e>>2]|0;if((c[f>>2]|0)>=(c[(c[d>>2]|0)+32>>2]|0)){break}a=(c[g+28>>2]|0)+((Z(c[f>>2]|0,c[(c[e>>2]|0)+36>>2]|0)|0)<<2)|0;c[(c[(c[e>>2]|0)+20>>2]|0)+(c[f>>2]<<2)>>2]=a;c[f>>2]=(c[f>>2]|0)+1}i=b;return g|0}function hf(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0;g=i;i=i+32|0;h=g+24|0;j=g+20|0;k=g+16|0;l=g+12|0;m=g+8|0;n=g+4|0;o=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[o>>2]=sd(40)|0;c[c[o>>2]>>2]=1;c[(c[o>>2]|0)+32>>2]=c[m>>2];c[(c[o>>2]|0)+36>>2]=c[l>>2];c[(c[o>>2]|0)+4>>2]=c[h>>2];c[(c[o>>2]|0)+8>>2]=c[j>>2];c[(c[o>>2]|0)+12>>2]=c[k>>2];j=sd(c[k>>2]<<2)|0;c[(c[o>>2]|0)+16>>2]=j;j=sd((Z(c[m>>2]|0,c[l>>2]|0)|0)<<2)|0;c[(c[o>>2]|0)+28>>2]=j;j=sd(c[m>>2]<<2)|0;c[(c[o>>2]|0)+20>>2]=j;j=sd(c[m>>2]<<2)|0;c[(c[o>>2]|0)+24>>2]=j;c[n>>2]=0;while(1){p=c[o>>2]|0;if((c[n>>2]|0)>=(c[m>>2]|0)){break}j=(c[p+28>>2]|0)+((Z(c[n>>2]|0,c[l>>2]|0)|0)<<2)|0;c[(c[(c[o>>2]|0)+20>>2]|0)+(c[n>>2]<<2)>>2]=j;c[n>>2]=(c[n>>2]|0)+1}i=g;return p|0}function jf(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+8|0;e=b+4|0;f=b;c[d>>2]=a;c[e>>2]=sd(32)|0;c[f>>2]=c[c[d>>2]>>2];d=sd(Z(c[f>>2]|0,c[f>>2]|0)|0)|0;c[c[e>>2]>>2]=d;d=sd(c[f>>2]|0)|0;c[(c[e>>2]|0)+4>>2]=d;d=sd(c[f>>2]|0)|0;c[(c[e>>2]|0)+8>>2]=d;d=sd(c[f>>2]|0)|0;c[(c[e>>2]|0)+12>>2]=d;d=sd((c[f>>2]|0)*5<<2)|0;c[(c[e>>2]|0)+16>>2]=d;d=sd((Z(c[f>>2]|0,c[f>>2]|0)|0)<<2)|0;c[(c[e>>2]|0)+20>>2]=d;d=sd((Z(c[f>>2]|0,c[f>>2]|0)|0)<<2)|0;c[(c[e>>2]|0)+24>>2]=d;d=sd(c[f>>2]<<2)|0;c[(c[e>>2]|0)+28>>2]=d;i=b;return c[e>>2]|0}function kf(b,e,f,g){b=b|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;h=i;i=i+48|0;j=h+32|0;k=h+28|0;l=h+24|0;m=h+20|0;n=h+16|0;o=h+12|0;p=h+8|0;q=h+4|0;r=h;c[j>>2]=b;c[k>>2]=e;c[l>>2]=f;c[m>>2]=g;c[n>>2]=c[c[j>>2]>>2];g=Z(c[l>>2]|0,c[n>>2]|0)|0;c[o>>2]=g+(c[k>>2]|0);g=Z(c[l>>2]|0,c[c[j>>2]>>2]|0)|0;f=Z(g+(c[k>>2]|0)|0,c[c[j>>2]>>2]|0)|0;if((d[(c[(c[j>>2]|0)+16>>2]|0)+(f+(c[m>>2]|0)-1)|0]|0|0)==0){Ba(5672,4528,772,5688)}c[p>>2]=1;while(1){if((c[p>>2]|0)>(c[n>>2]|0)){break}if((c[p>>2]|0)!=(c[m>>2]|0)){f=Z(c[l>>2]|0,c[c[j>>2]>>2]|0)|0;g=Z(f+(c[k>>2]|0)|0,c[c[j>>2]>>2]|0)|0;a[(c[(c[j>>2]|0)+16>>2]|0)+(g+(c[p>>2]|0)-1)|0]=0}c[p>>2]=(c[p>>2]|0)+1}c[p>>2]=0;while(1){if((c[p>>2]|0)>=(c[n>>2]|0)){break}if((c[p>>2]|0)!=(c[l>>2]|0)){g=Z(c[p>>2]|0,c[c[j>>2]>>2]|0)|0;f=Z(g+(c[k>>2]|0)|0,c[c[j>>2]>>2]|0)|0;a[(c[(c[j>>2]|0)+16>>2]|0)+(f+(c[m>>2]|0)-1)|0]=0}c[p>>2]=(c[p>>2]|0)+1}c[p>>2]=0;while(1){if((c[p>>2]|0)>=(c[n>>2]|0)){break}if((c[p>>2]|0)!=(c[k>>2]|0)){f=Z(c[l>>2]|0,c[c[j>>2]>>2]|0)|0;g=Z(f+(c[p>>2]|0)|0,c[c[j>>2]>>2]|0)|0;a[(c[(c[j>>2]|0)+16>>2]|0)+(g+(c[m>>2]|0)-1)|0]=0}c[p>>2]=(c[p>>2]|0)+1}c[q>>2]=c[(c[(c[(c[j>>2]|0)+4>>2]|0)+16>>2]|0)+(c[o>>2]<<2)>>2];c[p>>2]=0;while(1){if((c[p>>2]|0)>=(c[n>>2]|0)){break}c[r>>2]=c[(c[(c[(c[(c[j>>2]|0)+4>>2]|0)+20>>2]|0)+(c[q>>2]<<2)>>2]|0)+(c[p>>2]<<2)>>2];if((c[r>>2]|0)!=(c[o>>2]|0)){g=Z(c[r>>2]|0,c[c[j>>2]>>2]|0)|0;a[(c[(c[j>>2]|0)+16>>2]|0)+(g+(c[m>>2]|0)-1)|0]=0}c[p>>2]=(c[p>>2]|0)+1}a[(c[(c[j>>2]|0)+20>>2]|0)+(c[o>>2]|0)|0]=c[m>>2];r=Z(c[q>>2]|0,c[n>>2]|0)|0;a[(c[(c[j>>2]|0)+40>>2]|0)+(r+(c[m>>2]|0)-1)|0]=1;r=Z(c[k>>2]|0,c[n>>2]|0)|0;a[(c[(c[j>>2]|0)+36>>2]|0)+(r+(c[m>>2]|0)-1)|0]=1;r=Z(c[l>>2]|0,c[n>>2]|0)|0;a[(c[(c[j>>2]|0)+32>>2]|0)+(r+(c[m>>2]|0)-1)|0]=1;if((c[(c[j>>2]|0)+44>>2]|0)==0){i=h;return}if(((c[o>>2]|0)%((c[n>>2]|0)+1|0)|0|0)==0){c[p>>2]=0;while(1){if((c[p>>2]|0)>=(c[n>>2]|0)){break}r=Z(c[p>>2]|0,(c[n>>2]|0)+1|0)|0;if((r|0)!=(c[o>>2]|0)){r=Z(c[p>>2]|0,(c[n>>2]|0)+1|0)|0;l=Z(r,c[c[j>>2]>>2]|0)|0;a[(c[(c[j>>2]|0)+16>>2]|0)+(l+(c[m>>2]|0)-1)|0]=0}c[p>>2]=(c[p>>2]|0)+1}a[(c[(c[j>>2]|0)+44>>2]|0)+((c[m>>2]|0)-1)|0]=1}if(!(((c[o>>2]|0)%((c[n>>2]|0)-1|0)|0|0)==0&(c[o>>2]|0)>0)){i=h;return}if((c[o>>2]|0)>=((Z(c[n>>2]|0,c[n>>2]|0)|0)-1|0)){i=h;return}c[p>>2]=0;while(1){if((c[p>>2]|0)>=(c[n>>2]|0)){break}l=Z((c[p>>2]|0)+1|0,(c[n>>2]|0)-1|0)|0;if((l|0)!=(c[o>>2]|0)){l=Z((c[p>>2]|0)+1|0,(c[n>>2]|0)-1|0)|0;r=Z(l,c[c[j>>2]>>2]|0)|0;a[(c[(c[j>>2]|0)+16>>2]|0)+(r+(c[m>>2]|0)-1)|0]=0}c[p>>2]=(c[p>>2]|0)+1}a[(c[(c[j>>2]|0)+44>>2]|0)+((c[n>>2]|0)+(c[m>>2]|0)-1)|0]=1;i=h;return}function lf(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0;e=i;i=i+48|0;f=e+36|0;g=e+32|0;h=e+28|0;j=e+24|0;k=e+20|0;l=e+16|0;m=e+12|0;n=e+8|0;o=e+4|0;p=e;c[g>>2]=b;c[h>>2]=d;c[j>>2]=c[c[g>>2]>>2];c[l>>2]=0;c[k>>2]=-1;c[m>>2]=0;while(1){if((c[m>>2]|0)>=(c[j>>2]|0)){break}if((a[(c[(c[g>>2]|0)+16>>2]|0)+(c[(c[h>>2]|0)+(c[m>>2]<<2)>>2]|0)|0]|0)!=0){c[k>>2]=c[(c[h>>2]|0)+(c[m>>2]<<2)>>2];c[l>>2]=(c[l>>2]|0)+1}c[m>>2]=(c[m>>2]|0)+1}if((c[l>>2]|0)==1){if((c[k>>2]|0)<0){Ba(5640,4528,874,5656)}c[p>>2]=1+((c[k>>2]|0)%(c[j>>2]|0)|0);c[n>>2]=(c[k>>2]|0)/(c[j>>2]|0)|0;c[o>>2]=(c[n>>2]|0)/(c[j>>2]|0)|0;c[n>>2]=(c[n>>2]|0)%(c[j>>2]|0)|0;k=Z(c[o>>2]|0,c[j>>2]|0)|0;if((a[(c[(c[g>>2]|0)+20>>2]|0)+(k+(c[n>>2]|0))|0]|0)==0){kf(c[g>>2]|0,c[n>>2]|0,c[o>>2]|0,c[p>>2]|0);c[f>>2]=1;q=c[f>>2]|0;i=e;return q|0}}else{if((c[l>>2]|0)==0){c[f>>2]=-1;q=c[f>>2]|0;i=e;return q|0}}c[f>>2]=0;q=c[f>>2]|0;i=e;return q|0}function mf(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0;e=i;i=i+32|0;f=e+16|0;g=e+12|0;h=e+8|0;j=e+4|0;k=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;c[(c[(c[f>>2]|0)+16>>2]|0)+(c[h>>2]<<2)>>2]=-1;c[k>>2]=0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[(c[(c[f>>2]|0)+24>>2]|0)+(c[g>>2]<<2)>>2]|0)){break}if((c[(c[(c[(c[f>>2]|0)+20>>2]|0)+(c[g>>2]<<2)>>2]|0)+(c[j>>2]<<2)>>2]|0)!=(c[h>>2]|0)){d=c[(c[(c[(c[f>>2]|0)+20>>2]|0)+(c[g>>2]<<2)>>2]|0)+(c[j>>2]<<2)>>2]|0;b=c[k>>2]|0;c[k>>2]=b+1;c[(c[(c[(c[f>>2]|0)+20>>2]|0)+(c[g>>2]<<2)>>2]|0)+(b<<2)>>2]=d}c[j>>2]=(c[j>>2]|0)+1}if(((c[k>>2]|0)+1|0)==(c[j>>2]|0)){j=(c[(c[f>>2]|0)+24>>2]|0)+(c[g>>2]<<2)|0;c[j>>2]=(c[j>>2]|0)+ -1;i=e;return}else{Ba(5600,4528,640,5616)}}function nf(b,e,f,g){b=b|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0;h=i;i=i+48|0;j=h+40|0;k=h+36|0;l=h+32|0;m=h+28|0;n=h+24|0;o=h+20|0;p=h+16|0;q=h+12|0;r=h+8|0;s=h+4|0;t=h;c[j>>2]=b;c[k>>2]=e;c[l>>2]=f;c[m>>2]=g;c[c[m>>2]>>2]=0;c[p>>2]=0;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[l>>2]|0)){break}g=c[(c[k>>2]|0)+(c[o>>2]<<2)>>2]|0;if((a[(c[(c[j>>2]|0)+20>>2]|0)+(c[(c[k>>2]|0)+(c[o>>2]<<2)>>2]|0)|0]|0)!=0){f=c[m>>2]|0;c[f>>2]=(c[f>>2]|0)+(d[(c[(c[j>>2]|0)+20>>2]|0)+g|0]|0)}else{f=c[p>>2]|0;c[p>>2]=f+1;c[(c[k>>2]|0)+(f<<2)>>2]=g}c[o>>2]=(c[o>>2]|0)+1}c[l>>2]=c[p>>2];c[q>>2]=0;c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[(c[(c[j>>2]|0)+8>>2]|0)+32>>2]|0)){break}if((c[q>>2]|0)>=(c[l>>2]|0)){break}c[r>>2]=c[(c[(c[(c[j>>2]|0)+8>>2]|0)+24>>2]|0)+(c[n>>2]<<2)>>2];c[s>>2]=0;do{if((c[r>>2]|0)!=0){c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[r>>2]|0)){break}c[p>>2]=c[q>>2];while(1){if((c[p>>2]|0)>=(c[l>>2]|0)){break}if((c[(c[k>>2]|0)+(c[p>>2]<<2)>>2]|0)==(c[(c[(c[(c[(c[j>>2]|0)+8>>2]|0)+20>>2]|0)+(c[n>>2]<<2)>>2]|0)+(c[o>>2]<<2)>>2]|0)){u=16;break}c[p>>2]=(c[p>>2]|0)+1}if((u|0)==16){u=0;c[t>>2]=c[(c[k>>2]|0)+((c[q>>2]|0)+(c[s>>2]|0)<<2)>>2];c[(c[k>>2]|0)+((c[q>>2]|0)+(c[s>>2]|0)<<2)>>2]=c[(c[k>>2]|0)+(c[p>>2]<<2)>>2];c[(c[k>>2]|0)+(c[p>>2]<<2)>>2]=c[t>>2];c[s>>2]=(c[s>>2]|0)+1}c[o>>2]=(c[o>>2]|0)+1}if((c[s>>2]|0)!=(c[(c[(c[(c[j>>2]|0)+8>>2]|0)+24>>2]|0)+(c[n>>2]<<2)>>2]|0)){c[q>>2]=(c[q>>2]|0)+(c[s>>2]|0);break}else{fg((c[k>>2]|0)+(c[q>>2]<<2)|0,(c[k>>2]|0)+(c[q>>2]<<2)+(c[s>>2]<<2)|0,(c[l>>2]|0)-(c[q>>2]|0)-(c[s>>2]|0)<<2|0)|0;c[l>>2]=(c[l>>2]|0)-(c[s>>2]|0);g=c[m>>2]|0;c[g>>2]=(c[g>>2]|0)+(d[(c[(c[j>>2]|0)+24>>2]|0)+(c[n>>2]|0)|0]|0);break}}}while(0);c[n>>2]=(c[n>>2]|0)+1}if((c[q>>2]|0)==(c[l>>2]|0)){i=h;return c[q>>2]|0}else{Ba(5560,4528,1639,5576)}return 0}function of(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0;e=i;i=i+48|0;f=e+32|0;g=e+28|0;h=e+24|0;j=e+20|0;k=e+16|0;l=e+12|0;m=e+8|0;n=e+4|0;o=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;c[l>>2]=c[(c[(c[f>>2]|0)+16>>2]|0)+(c[c[g>>2]>>2]<<2)>>2];c[m>>2]=c[(c[f>>2]|0)+32>>2];if((c[(c[f>>2]|0)+36>>2]|0)<(c[h>>2]|0)){Ba(5416,4528,604,5448)}if((c[(c[(c[f>>2]|0)+24>>2]|0)+(c[l>>2]<<2)>>2]|0)<=(c[h>>2]|0)){Ba(5464,4528,605,5448)}d=(c[f>>2]|0)+32|0;c[d>>2]=(c[d>>2]|0)+1;d=ud(c[(c[f>>2]|0)+28>>2]|0,(Z(c[(c[f>>2]|0)+32>>2]|0,c[(c[f>>2]|0)+36>>2]|0)|0)<<2)|0;c[(c[f>>2]|0)+28>>2]=d;d=ud(c[(c[f>>2]|0)+24>>2]|0,c[(c[f>>2]|0)+32>>2]<<2)|0;c[(c[f>>2]|0)+24>>2]=d;td(c[(c[f>>2]|0)+20>>2]|0);d=sd(c[(c[f>>2]|0)+32>>2]<<2)|0;c[(c[f>>2]|0)+20>>2]=d;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[(c[f>>2]|0)+32>>2]|0)){break}d=(c[(c[f>>2]|0)+28>>2]|0)+((Z(c[j>>2]|0,c[(c[f>>2]|0)+36>>2]|0)|0)<<2)|0;c[(c[(c[f>>2]|0)+20>>2]|0)+(c[j>>2]<<2)>>2]=d;c[j>>2]=(c[j>>2]|0)+1}c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[h>>2]|0)){break}if((c[(c[(c[f>>2]|0)+16>>2]|0)+(c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]<<2)>>2]|0)!=(c[l>>2]|0)){p=11;break}c[(c[(c[f>>2]|0)+16>>2]|0)+(c[(c[g>>2]|0)+(c[j>>2]<<2)>>2]<<2)>>2]=c[m>>2];c[(c[(c[(c[f>>2]|0)+20>>2]|0)+(c[m>>2]<<2)>>2]|0)+(c[j>>2]<<2)>>2]=c[(c[g>>2]|0)+(c[j>>2]<<2)>>2];c[j>>2]=(c[j>>2]|0)+1}if((p|0)==11){Ba(5512,4528,616,5448)}c[k>>2]=0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[(c[(c[f>>2]|0)+24>>2]|0)+(c[l>>2]<<2)>>2]|0)){break}c[o>>2]=c[(c[(c[(c[f>>2]|0)+20>>2]|0)+(c[l>>2]<<2)>>2]|0)+(c[j>>2]<<2)>>2];c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[h>>2]|0)){break}if((c[(c[g>>2]|0)+(c[n>>2]<<2)>>2]|0)==(c[o>>2]|0)){break}c[n>>2]=(c[n>>2]|0)+1}if((c[n>>2]|0)==(c[h>>2]|0)){p=c[o>>2]|0;d=c[k>>2]|0;c[k>>2]=d+1;c[(c[(c[(c[f>>2]|0)+20>>2]|0)+(c[l>>2]<<2)>>2]|0)+(d<<2)>>2]=p}c[j>>2]=(c[j>>2]|0)+1}j=(c[(c[f>>2]|0)+24>>2]|0)+(c[l>>2]<<2)|0;c[j>>2]=(c[j>>2]|0)-(c[h>>2]|0);c[(c[(c[f>>2]|0)+24>>2]|0)+(c[m>>2]<<2)>>2]=c[h>>2];i=e;return}function pf(b,e,f,g){b=b|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0;h=i;i=i+64|0;j=h+60|0;k=h+56|0;l=h+52|0;m=h+48|0;n=h+44|0;o=h+40|0;p=h+36|0;q=h+32|0;r=h+28|0;s=h+24|0;t=h+20|0;u=h+16|0;v=h+12|0;w=h+8|0;x=h+4|0;y=h;c[k>>2]=b;c[l>>2]=e;c[m>>2]=f;c[n>>2]=g;c[o>>2]=c[c[k>>2]>>2];c[q>>2]=0;c[r>>2]=c[(c[(c[l>>2]|0)+24>>2]|0)+(c[n>>2]<<2)>>2];if((d[(c[m>>2]|0)+(c[n>>2]|0)|0]|0)==0){c[j>>2]=0;z=c[j>>2]|0;i=h;return z|0}c[p>>2]=0;while(1){if((c[p>>2]|0)>=(c[r>>2]|0)){break}c[t>>2]=c[(c[(c[(c[l>>2]|0)+20>>2]|0)+(c[n>>2]<<2)>>2]|0)+(c[p>>2]<<2)>>2];c[s>>2]=1;while(1){if((c[s>>2]|0)>(c[o>>2]|0)){break}g=Z(c[t>>2]|0,c[c[k>>2]>>2]|0)|0;if((a[(c[(c[k>>2]|0)+16>>2]|0)+(g+(c[s>>2]|0)-1)|0]|0)!=0){c[u>>2]=0;c[v>>2]=0;c[w>>2]=0;while(1){if((c[w>>2]|0)>=(c[r>>2]|0)){break}c[y>>2]=c[(c[(c[(c[l>>2]|0)+20>>2]|0)+(c[n>>2]<<2)>>2]|0)+(c[w>>2]<<2)>>2];a:do{if((c[p>>2]|0)!=(c[w>>2]|0)){c[x>>2]=1;while(1){if((c[x>>2]|0)>(c[o>>2]|0)){break}g=Z(c[y>>2]|0,c[c[k>>2]>>2]|0)|0;A=c[x>>2]|0;if((a[(c[(c[k>>2]|0)+16>>2]|0)+(g+(c[x>>2]|0)-1)|0]|0)!=0){B=14;break}c[x>>2]=A+1}if((B|0)==14){B=0;c[v>>2]=(c[v>>2]|0)+A}c[x>>2]=c[o>>2];while(1){if((c[x>>2]|0)<=0){break a}g=Z(c[y>>2]|0,c[c[k>>2]>>2]|0)|0;C=c[x>>2]|0;if((a[(c[(c[k>>2]|0)+16>>2]|0)+(g+(c[x>>2]|0)-1)|0]|0)!=0){break}c[x>>2]=C+ -1}c[u>>2]=(c[u>>2]|0)+C}}while(0);c[w>>2]=(c[w>>2]|0)+1}if(((c[u>>2]|0)+(c[s>>2]|0)|0)<(d[(c[m>>2]|0)+(c[n>>2]|0)|0]|0)){g=Z(c[t>>2]|0,c[c[k>>2]>>2]|0)|0;a[(c[(c[k>>2]|0)+16>>2]|0)+(g+(c[s>>2]|0)-1)|0]=0;c[q>>2]=1}if(((c[v>>2]|0)+(c[s>>2]|0)|0)>(d[(c[m>>2]|0)+(c[n>>2]|0)|0]|0)){g=Z(c[t>>2]|0,c[c[k>>2]>>2]|0)|0;a[(c[(c[k>>2]|0)+16>>2]|0)+(g+(c[s>>2]|0)-1)|0]=0;c[q>>2]=1}}c[s>>2]=(c[s>>2]|0)+1}c[p>>2]=(c[p>>2]|0)+1}c[j>>2]=c[q>>2];z=c[j>>2]|0;i=h;return z|0}function qf(b,e,f,g,h){b=b|0;e=e|0;f=f|0;g=g|0;h=h|0;var j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0;j=i;i=i+96|0;k=j+92|0;l=j+88|0;m=j+84|0;n=j+80|0;o=j+76|0;p=j+72|0;q=j+68|0;r=j+64|0;s=j+60|0;t=j+56|0;u=j+52|0;v=j+48|0;w=j+44|0;x=j+40|0;y=j+36|0;z=j+32|0;A=j+28|0;B=j+24|0;C=j+20|0;D=j+16|0;E=j+12|0;F=j+8|0;G=j+4|0;H=j;c[l>>2]=b;c[m>>2]=e;c[n>>2]=f;c[o>>2]=g;c[p>>2]=h;c[q>>2]=c[c[l>>2]>>2];c[u>>2]=c[(c[(c[n>>2]|0)+24>>2]|0)+(c[m>>2]<<2)>>2];h=c[u>>2]|0;if((c[o>>2]|0)==0){if((h|0)!=0){Ba(5336,4528,1471,5352)}c[k>>2]=0;I=c[k>>2]|0;i=j;return I|0}if((h|0)<=0){Ba(5376,4528,1474,5352)}if((c[u>>2]|0)<2|(c[u>>2]|0)>4){c[k>>2]=0;I=c[k>>2]|0;i=j;return I|0}if((c[p>>2]|0)==0){c[x>>2]=-1;c[y>>2]=-1;c[z>>2]=-1;c[r>>2]=0;while(1){if((c[r>>2]|0)>=(c[u>>2]|0)){break}c[A>>2]=c[(c[(c[(c[n>>2]|0)+20>>2]|0)+(c[m>>2]<<2)>>2]|0)+(c[r>>2]<<2)>>2];if((d[(c[(c[l>>2]|0)+20>>2]|0)+(c[A>>2]|0)|0]|0)!=0){J=13;break}if((c[r>>2]|0)!=0){if((c[x>>2]|0)!=((c[A>>2]|0)/(c[q>>2]|0)|0|0)){c[x>>2]=-1}if((c[y>>2]|0)!=((c[A>>2]|0)%(c[q>>2]|0)|0|0)){c[y>>2]=-1}if((c[z>>2]|0)!=(c[(c[(c[(c[l>>2]|0)+4>>2]|0)+16>>2]|0)+(c[A>>2]<<2)>>2]|0)){c[z>>2]=-1}}else{c[x>>2]=(c[A>>2]|0)/(c[q>>2]|0)|0;c[y>>2]=(c[A>>2]|0)%(c[q>>2]|0)|0;c[z>>2]=c[(c[(c[(c[l>>2]|0)+4>>2]|0)+16>>2]|0)+(c[A>>2]<<2)>>2]}c[r>>2]=(c[r>>2]|0)+1}if((J|0)==13){Ba(5392,4528,1488,5352)}if(((c[z>>2]|0)==-1?(c[y>>2]|0)==-1:0)?(c[x>>2]|0)==-1:0){c[k>>2]=0;I=c[k>>2]|0;i=j;return I|0}}do{if((c[u>>2]|0)!=2){x=c[o>>2]|0;if((c[u>>2]|0)==3){if(!((x|0)<6|(c[o>>2]|0)>24)){c[v>>2]=2224+(c[o>>2]<<5);c[t>>2]=8;break}c[k>>2]=-1;I=c[k>>2]|0;i=j;return I|0}else{if(!((x|0)<10|(c[o>>2]|0)>30)){c[v>>2]=3024+((c[o>>2]|0)*48|0);c[t>>2]=12;break}c[k>>2]=-1;I=c[k>>2]|0;i=j;return I|0}}else{if(!((c[o>>2]|0)<3|(c[o>>2]|0)>17)){c[v>>2]=1864+((c[o>>2]|0)*20|0);c[t>>2]=5;break}c[k>>2]=-1;I=c[k>>2]|0;i=j;return I|0}}while(0);c[w>>2]=0;c[r>>2]=0;while(1){if((c[r>>2]|0)>=(c[t>>2]|0)){break}c[C>>2]=c[(c[v>>2]|0)+(c[r>>2]<<2)>>2];if((c[C>>2]|0)==0){break}c[B>>2]=0;while(1){if((c[B>>2]|0)>=(c[u>>2]|0)){break}c[E>>2]=c[C>>2];c[F>>2]=c[(c[(c[(c[n>>2]|0)+20>>2]|0)+(c[m>>2]<<2)>>2]|0)+(c[B>>2]<<2)>>2];c[D>>2]=1;while(1){if((c[D>>2]|0)>(c[q>>2]|0)){break}o=Z(c[F>>2]|0,c[c[l>>2]>>2]|0)|0;if((a[(c[(c[l>>2]|0)+16>>2]|0)+(o+(c[D>>2]|0)-1)|0]|0)==0){c[E>>2]=c[E>>2]&~(1<<c[D>>2])}c[D>>2]=(c[D>>2]|0)+1}if((c[E>>2]|0)==0){break}c[B>>2]=(c[B>>2]|0)+1}if((c[B>>2]|0)==(c[u>>2]|0)){c[w>>2]=c[w>>2]|c[C>>2]}c[r>>2]=(c[r>>2]|0)+1}if((c[w>>2]|0)==0){c[k>>2]=-1;I=c[k>>2]|0;i=j;return I|0}c[s>>2]=0;c[r>>2]=0;while(1){if((c[r>>2]|0)>=(c[u>>2]|0)){break}c[H>>2]=c[(c[(c[(c[n>>2]|0)+20>>2]|0)+(c[m>>2]<<2)>>2]|0)+(c[r>>2]<<2)>>2];c[G>>2]=1;while(1){if((c[G>>2]|0)>(c[q>>2]|0)){break}C=Z(c[H>>2]|0,c[c[l>>2]>>2]|0)|0;if((a[(c[(c[l>>2]|0)+16>>2]|0)+(C+(c[G>>2]|0)-1)|0]|0)!=0?(c[w>>2]&1<<c[G>>2]|0)==0:0){C=Z(c[H>>2]|0,c[c[l>>2]>>2]|0)|0;a[(c[(c[l>>2]|0)+16>>2]|0)+(C+(c[G>>2]|0)-1)|0]=0;c[s>>2]=1}c[G>>2]=(c[G>>2]|0)+1}c[r>>2]=(c[r>>2]|0)+1}c[k>>2]=c[s>>2];I=c[k>>2]|0;i=j;return I|0}function rf(b,e,f){b=b|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0;g=i;i=i+48|0;h=g+36|0;j=g+32|0;k=g+28|0;l=g+24|0;m=g+20|0;n=g+16|0;o=g+12|0;p=g+8|0;q=g+4|0;r=g;c[j>>2]=b;c[k>>2]=e;c[l>>2]=f;c[m>>2]=c[c[j>>2]>>2];c[p>>2]=0;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[m>>2]|0)){break}c[q>>2]=c[(c[k>>2]|0)+(c[o>>2]<<2)>>2];while(1){if((c[p>>2]|0)>=(c[m>>2]|0)){break}if((c[(c[l>>2]|0)+(c[p>>2]<<2)>>2]|0)>=(c[q>>2]|0)){break}c[p>>2]=(c[p>>2]|0)+1}if((a[(c[(c[j>>2]|0)+16>>2]|0)+(c[q>>2]|0)|0]|0)!=0){if((c[p>>2]|0)>=(c[m>>2]|0)){s=10;break}if((c[(c[l>>2]|0)+(c[p>>2]<<2)>>2]|0)!=(c[q>>2]|0)){s=10;break}}c[o>>2]=(c[o>>2]|0)+1}if((s|0)==10){c[h>>2]=0;t=c[h>>2]|0;i=g;return t|0}c[n>>2]=0;c[p>>2]=0;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[m>>2]|0)){break}c[r>>2]=c[(c[l>>2]|0)+(c[o>>2]<<2)>>2];while(1){if((c[p>>2]|0)>=(c[m>>2]|0)){break}if((c[(c[k>>2]|0)+(c[p>>2]<<2)>>2]|0)>=(c[r>>2]|0)){break}c[p>>2]=(c[p>>2]|0)+1}do{if((d[(c[(c[j>>2]|0)+16>>2]|0)+(c[r>>2]|0)|0]|0)!=0){if((c[p>>2]|0)<(c[m>>2]|0)?(c[(c[k>>2]|0)+(c[p>>2]<<2)>>2]|0)==(c[r>>2]|0):0){break}c[n>>2]=1;a[(c[(c[j>>2]|0)+16>>2]|0)+(c[r>>2]|0)|0]=0}}while(0);c[o>>2]=(c[o>>2]|0)+1}c[h>>2]=c[n>>2];t=c[h>>2]|0;i=g;return t|0}function sf(b,e,f){b=b|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0;g=i;i=i+80|0;h=g+76|0;j=g+72|0;k=g+68|0;l=g+64|0;m=g+60|0;n=g+56|0;o=g+52|0;p=g+48|0;q=g+44|0;r=g+40|0;s=g+36|0;t=g+32|0;u=g+28|0;v=g+24|0;w=g+20|0;x=g+16|0;y=g+12|0;z=g+8|0;A=g+4|0;B=g;c[j>>2]=b;c[k>>2]=e;c[l>>2]=f;c[m>>2]=c[c[j>>2]>>2];c[r>>2]=c[c[k>>2]>>2];c[s>>2]=c[(c[k>>2]|0)+4>>2];c[t>>2]=c[(c[k>>2]|0)+8>>2];c[u>>2]=c[(c[k>>2]|0)+12>>2];cg(c[s>>2]|0,1,c[m>>2]|0)|0;cg(c[t>>2]|0,1,c[m>>2]|0)|0;c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[m>>2]|0)){break}c[v>>2]=0;c[w>>2]=-1;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[m>>2]|0)){break}k=Z(c[n>>2]|0,c[m>>2]|0)|0;if((a[(c[(c[j>>2]|0)+16>>2]|0)+(c[(c[l>>2]|0)+(k+(c[o>>2]|0)<<2)>>2]|0)|0]|0)!=0){c[w>>2]=c[o>>2];c[v>>2]=(c[v>>2]|0)+1}c[o>>2]=(c[o>>2]|0)+1}if((c[v>>2]|0)<=0){C=9;break}if((c[v>>2]|0)==1){a[(c[t>>2]|0)+(c[w>>2]|0)|0]=0;a[(c[s>>2]|0)+(c[n>>2]|0)|0]=0}c[n>>2]=(c[n>>2]|0)+1}if((C|0)==9){Ba(5296,4528,1027,5312)}c[o>>2]=0;c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[m>>2]|0)){break}if((a[(c[s>>2]|0)+(c[n>>2]|0)|0]|0)!=0){w=c[n>>2]&255;v=c[o>>2]|0;c[o>>2]=v+1;a[(c[s>>2]|0)+v|0]=w}c[n>>2]=(c[n>>2]|0)+1}c[p>>2]=c[o>>2];c[o>>2]=0;c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[m>>2]|0)){break}if((a[(c[t>>2]|0)+(c[n>>2]|0)|0]|0)!=0){w=c[n>>2]&255;v=c[o>>2]|0;c[o>>2]=v+1;a[(c[t>>2]|0)+v|0]=w}c[n>>2]=(c[n>>2]|0)+1}if((c[p>>2]|0)!=(c[o>>2]|0)){Ba(5328,4528,1043,5312)}c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[p>>2]|0)){break}c[o>>2]=0;while(1){D=c[n>>2]|0;if((c[o>>2]|0)>=(c[p>>2]|0)){break}w=Z(d[(c[s>>2]|0)+D|0]|0,c[m>>2]|0)|0;v=Z(c[n>>2]|0,c[m>>2]|0)|0;a[(c[r>>2]|0)+(v+(c[o>>2]|0))|0]=a[(c[(c[j>>2]|0)+16>>2]|0)+(c[(c[l>>2]|0)+(w+(d[(c[t>>2]|0)+(c[o>>2]|0)|0]|0)<<2)>>2]|0)|0]|0;c[o>>2]=(c[o>>2]|0)+1}c[n>>2]=D+1}cg(c[u>>2]|0,0,c[p>>2]|0)|0;c[q>>2]=0;while(1){if((c[q>>2]|0)>1?(c[q>>2]|0)<((c[p>>2]|0)-1|0):0){c[x>>2]=0;c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[p>>2]|0)){break}c[y>>2]=1;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[p>>2]|0)){break}if((d[(c[u>>2]|0)+(c[o>>2]|0)|0]|0)!=0?(D=Z(c[n>>2]|0,c[m>>2]|0)|0,(d[(c[r>>2]|0)+(D+(c[o>>2]|0))|0]|0)!=0):0){C=40;break}c[o>>2]=(c[o>>2]|0)+1}if((C|0)==40){C=0;c[y>>2]=0}if((c[y>>2]|0)!=0){c[x>>2]=(c[x>>2]|0)+1}c[n>>2]=(c[n>>2]|0)+1}if((c[x>>2]|0)>((c[p>>2]|0)-(c[q>>2]|0)|0)){C=46;break}if((c[x>>2]|0)>=((c[p>>2]|0)-(c[q>>2]|0)|0)){c[z>>2]=0;c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[p>>2]|0)){break}c[A>>2]=1;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[p>>2]|0)){break}if((d[(c[u>>2]|0)+(c[o>>2]|0)|0]|0)!=0?(D=Z(c[n>>2]|0,c[m>>2]|0)|0,(d[(c[r>>2]|0)+(D+(c[o>>2]|0))|0]|0)!=0):0){C=54;break}c[o>>2]=(c[o>>2]|0)+1}if((C|0)==54){C=0;c[A>>2]=0}a:do{if((c[A>>2]|0)==0){c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[p>>2]|0)){break a}if((a[(c[u>>2]|0)+(c[o>>2]|0)|0]|0)==0?(D=Z(c[n>>2]|0,c[m>>2]|0)|0,(d[(c[r>>2]|0)+(D+(c[o>>2]|0))|0]|0)!=0):0){D=Z(d[(c[s>>2]|0)+(c[n>>2]|0)|0]|0,c[m>>2]|0)|0;c[B>>2]=c[(c[l>>2]|0)+(D+(d[(c[t>>2]|0)+(c[o>>2]|0)|0]|0)<<2)>>2];c[z>>2]=1;a[(c[(c[j>>2]|0)+16>>2]|0)+(c[B>>2]|0)|0]=0}c[o>>2]=(c[o>>2]|0)+1}}}while(0);c[n>>2]=(c[n>>2]|0)+1}if((c[z>>2]|0)!=0){C=65;break}}}c[n>>2]=c[p>>2];while(1){if((c[n>>2]|0)>0){E=(d[(c[u>>2]|0)+((c[n>>2]|0)-1)|0]|0)!=0}else{E=0}F=c[n>>2]|0;if(!E){break}D=F+ -1|0;c[n>>2]=D;a[(c[u>>2]|0)+D|0]=0;c[q>>2]=(c[q>>2]|0)+ -1}if((F|0)<=0){C=73;break}D=(c[n>>2]|0)+ -1|0;c[n>>2]=D;a[(c[u>>2]|0)+D|0]=1;c[q>>2]=(c[q>>2]|0)+1}if((C|0)==46){c[h>>2]=-1;G=c[h>>2]|0;i=g;return G|0}else if((C|0)==65){c[h>>2]=1;G=c[h>>2]|0;i=g;return G|0}else if((C|0)==73){c[h>>2]=0;G=c[h>>2]|0;i=g;return G|0}return 0}function tf(b,e){b=b|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0;f=i;i=i+112|0;g=f+100|0;h=f+96|0;j=f+92|0;k=f+88|0;l=f+84|0;m=f+80|0;n=f+76|0;o=f+72|0;p=f+68|0;q=f+64|0;r=f+60|0;s=f+56|0;t=f+52|0;u=f+48|0;v=f+44|0;w=f+40|0;x=f+36|0;y=f+32|0;z=f+28|0;A=f+24|0;B=f+20|0;C=f+16|0;D=f+12|0;E=f+8|0;F=f+4|0;G=f;c[h>>2]=b;c[j>>2]=e;c[k>>2]=c[c[h>>2]>>2];c[l>>2]=c[(c[j>>2]|0)+20>>2];c[m>>2]=c[c[j>>2]>>2];c[n>>2]=c[(c[j>>2]|0)+16>>2];c[p>>2]=0;a:while(1){if((c[p>>2]|0)>=(c[k>>2]|0)){H=66;break}c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[k>>2]|0)){break}c[r>>2]=0;c[q>>2]=0;c[s>>2]=1;while(1){if((c[s>>2]|0)>(c[k>>2]|0)){break}j=Z(c[p>>2]|0,c[c[h>>2]>>2]|0)|0;e=Z(j+(c[o>>2]|0)|0,c[c[h>>2]>>2]|0)|0;if((a[(c[(c[h>>2]|0)+16>>2]|0)+(e+(c[s>>2]|0)-1)|0]|0)!=0){c[q>>2]=(c[q>>2]|0)+1;c[r>>2]=(c[r>>2]|0)+(c[s>>2]|0)}c[s>>2]=(c[s>>2]|0)+1}b:do{if((c[q>>2]|0)==2){c[s>>2]=1;while(1){if((c[s>>2]|0)>(c[k>>2]|0)){break b}e=Z(c[p>>2]|0,c[c[h>>2]>>2]|0)|0;j=Z(e+(c[o>>2]|0)|0,c[c[h>>2]>>2]|0)|0;c:do{if((a[(c[(c[h>>2]|0)+16>>2]|0)+(j+(c[s>>2]|0)-1)|0]|0)!=0){c[t>>2]=c[s>>2];cg(c[m>>2]|0,(c[k>>2]|0)+1&255|0,Z(c[k>>2]|0,c[k>>2]|0)|0)|0;c[w>>2]=0;c[v>>2]=0;e=Z(c[p>>2]|0,c[k>>2]|0)|0;b=e+(c[o>>2]|0)|0;e=c[w>>2]|0;c[w>>2]=e+1;c[(c[l>>2]|0)+(e<<2)>>2]=b;b=Z(c[p>>2]|0,c[k>>2]|0)|0;a[(c[m>>2]|0)+(b+(c[o>>2]|0))|0]=(c[r>>2]|0)-(c[s>>2]|0);d:while(1){if((c[v>>2]|0)>=(c[w>>2]|0)){break c}b=c[v>>2]|0;c[v>>2]=b+1;c[x>>2]=c[(c[l>>2]|0)+(b<<2)>>2];c[y>>2]=(c[x>>2]|0)/(c[k>>2]|0)|0;c[x>>2]=(c[x>>2]|0)%(c[k>>2]|0)|0;b=Z(c[y>>2]|0,c[k>>2]|0)|0;c[u>>2]=d[(c[m>>2]|0)+(b+(c[x>>2]|0))|0]|0;c[z>>2]=0;c[B>>2]=0;while(1){if((c[B>>2]|0)>=(c[k>>2]|0)){break}b=Z(c[B>>2]|0,c[k>>2]|0)|0;e=b+(c[x>>2]|0)|0;b=c[z>>2]|0;c[z>>2]=b+1;c[(c[n>>2]|0)+(b<<2)>>2]=e;c[B>>2]=(c[B>>2]|0)+1}c[A>>2]=0;while(1){I=Z(c[y>>2]|0,c[k>>2]|0)|0;if((c[A>>2]|0)>=(c[k>>2]|0)){break}e=I+(c[A>>2]|0)|0;b=c[z>>2]|0;c[z>>2]=b+1;c[(c[n>>2]|0)+(b<<2)>>2]=e;c[A>>2]=(c[A>>2]|0)+1}c[A>>2]=c[(c[(c[(c[h>>2]|0)+4>>2]|0)+16>>2]|0)+(I+(c[x>>2]|0)<<2)>>2];c[B>>2]=0;while(1){if((c[B>>2]|0)>=(c[k>>2]|0)){break}e=c[(c[(c[(c[(c[h>>2]|0)+4>>2]|0)+20>>2]|0)+(c[A>>2]<<2)>>2]|0)+(c[B>>2]<<2)>>2]|0;b=c[z>>2]|0;c[z>>2]=b+1;c[(c[n>>2]|0)+(b<<2)>>2]=e;c[B>>2]=(c[B>>2]|0)+1}e:do{if((c[(c[h>>2]|0)+44>>2]|0)!=0){e=Z(c[y>>2]|0,c[k>>2]|0)|0;c[D>>2]=e+(c[x>>2]|0);f:do{if(((c[D>>2]|0)%((c[k>>2]|0)+1|0)|0|0)==0){c[C>>2]=0;while(1){if((c[C>>2]|0)>=(c[k>>2]|0)){break f}e=Z(c[C>>2]|0,(c[k>>2]|0)+1|0)|0;b=c[z>>2]|0;c[z>>2]=b+1;c[(c[n>>2]|0)+(b<<2)>>2]=e;c[C>>2]=(c[C>>2]|0)+1}}}while(0);if(((c[D>>2]|0)%((c[k>>2]|0)-1|0)|0|0)==0&(c[D>>2]|0)>0?(c[D>>2]|0)<((Z(c[k>>2]|0,c[k>>2]|0)|0)-1|0):0){c[C>>2]=0;while(1){if((c[C>>2]|0)>=(c[k>>2]|0)){break e}e=Z((c[C>>2]|0)+1|0,(c[k>>2]|0)-1|0)|0;b=c[z>>2]|0;c[z>>2]=b+1;c[(c[n>>2]|0)+(b<<2)>>2]=e;c[C>>2]=(c[C>>2]|0)+1}}}}while(0);c[C>>2]=0;while(1){if((c[C>>2]|0)>=(c[z>>2]|0)){continue d}c[A>>2]=(c[(c[n>>2]|0)+(c[C>>2]<<2)>>2]|0)%(c[k>>2]|0)|0;c[B>>2]=(c[(c[n>>2]|0)+(c[C>>2]<<2)>>2]|0)/(c[k>>2]|0)|0;e=Z(c[B>>2]|0,c[k>>2]|0)|0;do{if((d[(c[m>>2]|0)+(e+(c[A>>2]|0))|0]|0)>(c[k>>2]|0)?(b=Z(c[B>>2]|0,c[c[h>>2]>>2]|0)|0,J=Z(b+(c[A>>2]|0)|0,c[c[h>>2]>>2]|0)|0,(a[(c[(c[h>>2]|0)+16>>2]|0)+(J+(c[u>>2]|0)-1)|0]|0)!=0):0){if((c[A>>2]|0)==(c[x>>2]|0)?(c[B>>2]|0)==(c[y>>2]|0):0){break}c[F>>2]=0;c[E>>2]=0;c[G>>2]=1;while(1){if((c[G>>2]|0)>(c[k>>2]|0)){break}J=Z(c[B>>2]|0,c[c[h>>2]>>2]|0)|0;b=Z(J+(c[A>>2]|0)|0,c[c[h>>2]>>2]|0)|0;if((a[(c[(c[h>>2]|0)+16>>2]|0)+(b+(c[G>>2]|0)-1)|0]|0)!=0){c[E>>2]=(c[E>>2]|0)+1;c[F>>2]=(c[F>>2]|0)+(c[G>>2]|0)}c[G>>2]=(c[G>>2]|0)+1}if((c[E>>2]|0)==2){b=Z(c[B>>2]|0,c[k>>2]|0)|0;J=b+(c[A>>2]|0)|0;b=c[w>>2]|0;c[w>>2]=b+1;c[(c[l>>2]|0)+(b<<2)>>2]=J;J=Z(c[B>>2]|0,c[k>>2]|0)|0;a[(c[m>>2]|0)+(J+(c[A>>2]|0))|0]=(c[F>>2]|0)-(c[u>>2]|0)}if((c[u>>2]|0)==(c[t>>2]|0)){if((c[A>>2]|0)==(c[o>>2]|0)){H=61;break a}if((c[B>>2]|0)==(c[p>>2]|0)){H=61;break a}J=Z(c[B>>2]|0,c[k>>2]|0)|0;b=Z(c[p>>2]|0,c[k>>2]|0)|0;if((c[(c[(c[(c[h>>2]|0)+4>>2]|0)+16>>2]|0)+(J+(c[A>>2]|0)<<2)>>2]|0)==(c[(c[(c[(c[h>>2]|0)+4>>2]|0)+16>>2]|0)+(b+(c[o>>2]|0)<<2)>>2]|0)){H=61;break a}if((c[(c[h>>2]|0)+44>>2]|0)!=0){b=Z(c[B>>2]|0,c[k>>2]|0)|0;if(((b+(c[A>>2]|0)|0)%((c[k>>2]|0)+1|0)|0|0)==0?(b=Z(c[p>>2]|0,c[k>>2]|0)|0,((b+(c[o>>2]|0)|0)%((c[k>>2]|0)+1|0)|0|0)==0):0){H=61;break a}b=Z(c[B>>2]|0,c[k>>2]|0)|0;if(((((((b+(c[A>>2]|0)|0)%((c[k>>2]|0)-1|0)|0|0)==0?(b=Z(c[B>>2]|0,c[k>>2]|0)|0,(b+(c[A>>2]|0)|0)>0):0)?(b=Z(c[B>>2]|0,c[k>>2]|0)|0,(b+(c[A>>2]|0)|0)<((Z(c[k>>2]|0,c[k>>2]|0)|0)-1|0)):0)?(b=Z(c[p>>2]|0,c[k>>2]|0)|0,((b+(c[o>>2]|0)|0)%((c[k>>2]|0)-1|0)|0|0)==0):0)?(b=Z(c[p>>2]|0,c[k>>2]|0)|0,(b+(c[o>>2]|0)|0)>0):0)?(b=Z(c[p>>2]|0,c[k>>2]|0)|0,(b+(c[o>>2]|0)|0)<((Z(c[k>>2]|0,c[k>>2]|0)|0)-1|0)):0){H=61;break a}}}}}while(0);c[C>>2]=(c[C>>2]|0)+1}}}}while(0);c[s>>2]=(c[s>>2]|0)+1}}}while(0);c[o>>2]=(c[o>>2]|0)+1}c[p>>2]=(c[p>>2]|0)+1}if((H|0)==61){p=Z(c[B>>2]|0,c[c[h>>2]>>2]|0)|0;B=Z(p+(c[A>>2]|0)|0,c[c[h>>2]>>2]|0)|0;a[(c[(c[h>>2]|0)+16>>2]|0)+(B+(c[t>>2]|0)-1)|0]=0;c[g>>2]=1;K=c[g>>2]|0;i=f;return K|0}else if((H|0)==66){c[g>>2]=0;K=c[g>>2]|0;i=f;return K|0}return 0}function uf(a){a=a|0;var b=0,d=0,e=0;b=i;i=i+16|0;d=b;c[d>>2]=a;a=c[d>>2]|0;e=(c[a>>2]|0)+ -1|0;c[a>>2]=e;if((e|0)!=0){i=b;return}td(c[(c[d>>2]|0)+16>>2]|0);td(c[(c[d>>2]|0)+20>>2]|0);td(c[(c[d>>2]|0)+28>>2]|0);td(c[(c[d>>2]|0)+24>>2]|0);td(c[d>>2]|0);i=b;return}function vf(a){a=a|0;var b=0,d=0;b=i;i=i+16|0;d=b;c[d>>2]=a;td(c[(c[d>>2]|0)+20>>2]|0);td(c[(c[d>>2]|0)+16>>2]|0);td(c[(c[d>>2]|0)+12>>2]|0);td(c[(c[d>>2]|0)+8>>2]|0);td(c[(c[d>>2]|0)+4>>2]|0);td(c[c[d>>2]>>2]|0);td(c[(c[d>>2]|0)+24>>2]|0);td(c[(c[d>>2]|0)+28>>2]|0);td(c[d>>2]|0);i=b;return}function wf(){var a=0,b=0,d=0,e=0;a=i;i=i+16|0;b=a+4|0;d=a;c[b>>2]=3;while(1){if((c[b>>2]|0)>=31){e=18;break}if((c[b>>2]|0)<18){c[d>>2]=Bf(1864+((c[b>>2]|0)*20|0)|0,0,c[b>>2]|0,2,1,0)|0;if((c[d>>2]|0)>5){e=5;break}if((c[d>>2]|0)<5){c[1864+((c[b>>2]|0)*20|0)+(c[d>>2]<<2)>>2]=0}}if((c[b>>2]|0)<25){c[d>>2]=Bf(2224+(c[b>>2]<<5)|0,0,c[b>>2]|0,3,1,0)|0;if((c[d>>2]|0)>8){e=10;break}if((c[d>>2]|0)<8){c[2224+(c[b>>2]<<5)+(c[d>>2]<<2)>>2]=0}}c[d>>2]=Bf(3024+((c[b>>2]|0)*48|0)|0,0,c[b>>2]|0,4,1,0)|0;if((c[d>>2]|0)>12){e=14;break}if((c[d>>2]|0)<12){c[3024+((c[b>>2]|0)*48|0)+(c[d>>2]<<2)>>2]=0}c[b>>2]=(c[b>>2]|0)+1}if((e|0)==5){Ba(6120,4528,186,6136)}else if((e|0)==10){Ba(6160,4528,192,6136)}else if((e|0)==14){Ba(6176,4528,197,6136)}else if((e|0)==18){i=a;return}}function xf(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;f=i;i=i+32|0;g=f+20|0;h=f+16|0;j=f+12|0;k=f+8|0;l=f+4|0;m=f;c[g>>2]=b;c[h>>2]=d;c[j>>2]=e;c[k>>2]=0;a:while(1){if((a[c[g>>2]|0]|0)==0){n=19;break}if((a[c[g>>2]|0]|0)==44){n=19;break}e=c[g>>2]|0;c[g>>2]=e+1;c[l>>2]=a[e]|0;e=c[l>>2]|0;if((c[l>>2]|0)>=97&(c[l>>2]|0)<=122){c[m>>2]=e-97+1;if(((c[k>>2]|0)+(c[m>>2]|0)|0)>(c[j>>2]|0)){n=6;break}while(1){d=c[m>>2]|0;c[m>>2]=d+ -1;if((d|0)<=0){continue a}d=c[k>>2]|0;c[k>>2]=d+1;a[(c[h>>2]|0)+d|0]=0}}if((e|0)==95){continue}if(!((c[l>>2]|0)>48&(c[l>>2]|0)<=57)){n=18;break}if((c[k>>2]|0)>=(c[j>>2]|0)){n=13;break}d=(Zf((c[g>>2]|0)+ -1|0)|0)&255;b=c[k>>2]|0;c[k>>2]=b+1;a[(c[h>>2]|0)+b|0]=d;while(1){if((a[c[g>>2]|0]|0)<48){continue a}if((a[c[g>>2]|0]|0)>57){continue a}c[g>>2]=(c[g>>2]|0)+1}}if((n|0)==6){Ba(6032,4528,3799,6048)}else if((n|0)==13){Ba(6064,4528,3805,6048)}else if((n|0)==18){Ba(6080,4528,3810,6048)}else if((n|0)==19){if((c[k>>2]|0)==(c[j>>2]|0)){i=f;return c[g>>2]|0}else{Ba(6104,4528,3813,6048)}}return 0}function yf(b,d,e,f){b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0;g=i;i=i+64|0;h=g+60|0;j=g+56|0;k=g+52|0;l=g+48|0;m=g+44|0;n=g+40|0;o=g+36|0;p=g+32|0;q=g+28|0;r=g+24|0;s=g+20|0;t=g+16|0;u=g+12|0;v=g+8|0;w=g+4|0;x=g;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=c[c[j>>2]>>2];c[o>>2]=0;f=zc(c[m>>2]|0)|0;c[p>>2]=f;c[c[k>>2]>>2]=f;a:while(1){if((a[c[n>>2]|0]|0)!=0){y=(a[c[n>>2]|0]|0)!=44}else{y=0}z=c[n>>2]|0;if(!y){A=21;break}if((a[z]|0)==95){c[q>>2]=0}else{if((a[c[n>>2]|0]|0)<97){A=10;break}if((a[c[n>>2]|0]|0)>122){A=10;break}c[q>>2]=(a[c[n>>2]|0]|0)-97+1}c[n>>2]=(c[n>>2]|0)+1;c[r>>2]=(c[q>>2]|0)!=26;while(1){f=c[q>>2]|0;c[q>>2]=f+ -1;if((f|0)<=0){break}if((c[o>>2]|0)>=(Z(c[l>>2]<<1,(c[l>>2]|0)-1|0)|0)){A=14;break a}f=(c[o>>2]|0)<(Z(c[l>>2]|0,(c[l>>2]|0)-1|0)|0);k=(c[o>>2]|0)/((c[l>>2]|0)-1|0)|0;if(f){c[u>>2]=k;c[v>>2]=(c[o>>2]|0)%((c[l>>2]|0)-1|0)|0;f=Z(c[u>>2]|0,c[l>>2]|0)|0;c[s>>2]=f+(c[v>>2]|0);f=Z(c[u>>2]|0,c[l>>2]|0)|0;c[t>>2]=f+(c[v>>2]|0)+1}else{c[w>>2]=k-(c[l>>2]|0);c[x>>2]=(c[o>>2]|0)%((c[l>>2]|0)-1|0)|0;k=Z(c[x>>2]|0,c[l>>2]|0)|0;c[s>>2]=k+(c[w>>2]|0);k=Z((c[x>>2]|0)+1|0,c[l>>2]|0)|0;c[t>>2]=k+(c[w>>2]|0)}Cc(c[p>>2]|0,c[s>>2]|0,c[t>>2]|0);c[o>>2]=(c[o>>2]|0)+1}if((c[r>>2]|0)==0){continue}c[o>>2]=(c[o>>2]|0)+1}if((A|0)==10){td(c[p>>2]|0);c[h>>2]=5888;B=c[h>>2]|0;i=g;return B|0}else if((A|0)==14){td(c[p>>2]|0);c[h>>2]=5928;B=c[h>>2]|0;i=g;return B|0}else if((A|0)==21){c[c[j>>2]>>2]=z;if((c[o>>2]|0)!=((Z(c[l>>2]<<1,(c[l>>2]|0)-1|0)|0)+1|0)){td(c[p>>2]|0);c[h>>2]=5976;B=c[h>>2]|0;i=g;return B|0}else{c[h>>2]=0;B=c[h>>2]|0;i=g;return B|0}}return 0}function zf(a,b,d,e){a=a|0;b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0;f=i;i=i+48|0;g=f+32|0;h=f+28|0;j=f+24|0;k=f+20|0;l=f+16|0;m=f+12|0;n=f+8|0;o=f+4|0;p=f;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=Z(c[(c[h>>2]|0)+4>>2]|0,c[(c[h>>2]|0)+8>>2]|0)|0;c[m>>2]=Z(c[l>>2]|0,c[l>>2]|0)|0;c[o>>2]=0;c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[m>>2]|0)){break}c[(c[(c[h>>2]|0)+16>>2]|0)+(c[n>>2]<<2)>>2]=-1;c[n>>2]=(c[n>>2]|0)+1}c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[m>>2]|0)){break}c[p>>2]=Ac(c[g>>2]|0,c[n>>2]|0)|0;if((c[(c[(c[h>>2]|0)+16>>2]|0)+(c[p>>2]<<2)>>2]|0)<0){l=c[o>>2]|0;c[o>>2]=l+1;c[(c[(c[h>>2]|0)+16>>2]|0)+(c[p>>2]<<2)>>2]=l}c[(c[(c[h>>2]|0)+16>>2]|0)+(c[n>>2]<<2)>>2]=c[(c[(c[h>>2]|0)+16>>2]|0)+(c[p>>2]<<2)>>2];c[n>>2]=(c[n>>2]|0)+1}if((c[o>>2]|0)<(c[j>>2]|0)){Ba(5824,4528,3176,5872)}if((c[o>>2]|0)<=(c[k>>2]|0)){c[(c[h>>2]|0)+32>>2]=c[o>>2];i=f;return}else{Ba(5824,4528,3176,5872)}}function Af(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0,j=0;b=i;i=i+16|0;d=b+12|0;e=b+8|0;f=b+4|0;g=b;c[d>>2]=a;c[e>>2]=0;while(1){if((c[e>>2]|0)>=(c[(c[d>>2]|0)+32>>2]|0)){break}c[(c[(c[(c[d>>2]|0)+20>>2]|0)+(c[e>>2]<<2)>>2]|0)+((c[(c[d>>2]|0)+36>>2]|0)-1<<2)>>2]=0;c[(c[(c[d>>2]|0)+24>>2]|0)+(c[e>>2]<<2)>>2]=0;c[e>>2]=(c[e>>2]|0)+1}c[e>>2]=0;while(1){if((c[e>>2]|0)>=(c[(c[d>>2]|0)+12>>2]|0)){h=9;break}c[f>>2]=c[(c[(c[d>>2]|0)+16>>2]|0)+(c[e>>2]<<2)>>2];a=(c[(c[(c[d>>2]|0)+20>>2]|0)+(c[f>>2]<<2)>>2]|0)+((c[(c[d>>2]|0)+36>>2]|0)-1<<2)|0;j=c[a>>2]|0;c[a>>2]=j+1;c[g>>2]=j;if((c[g>>2]|0)>=(c[(c[d>>2]|0)+36>>2]|0)){h=7;break}c[(c[(c[(c[d>>2]|0)+20>>2]|0)+(c[f>>2]<<2)>>2]|0)+(c[g>>2]<<2)>>2]=c[e>>2];j=(c[(c[d>>2]|0)+24>>2]|0)+(c[f>>2]<<2)|0;c[j>>2]=(c[j>>2]|0)+1;c[e>>2]=(c[e>>2]|0)+1}if((h|0)==7){Ba(5760,4528,3191,5792)}else if((h|0)==9){i=b;return}}function Bf(a,b,d,e,f,g){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0;h=i;i=i+48|0;j=h+32|0;k=h+28|0;l=h+24|0;m=h+20|0;n=h+16|0;o=h+12|0;p=h+8|0;q=h+4|0;r=h;c[j>>2]=a;c[k>>2]=b;c[l>>2]=d;c[m>>2]=e;c[n>>2]=f;c[o>>2]=g;if((c[m>>2]|0)<2){Ba(6192,4528,158,6216)}c[p>>2]=c[n>>2];while(1){if((c[p>>2]|0)>=(c[l>>2]|0)){s=13;break}c[q>>2]=c[o>>2]|1<<c[p>>2];if((c[o>>2]|0)==(c[q>>2]|0)){s=6;break}if((c[m>>2]|0)==2){c[r>>2]=(c[l>>2]|0)-(c[p>>2]|0);if((c[r>>2]|0)<=(c[p>>2]|0)){s=13;break}if((c[r>>2]|0)<=9){n=c[q>>2]|1<<c[r>>2];g=c[k>>2]|0;c[k>>2]=g+1;c[(c[j>>2]|0)+(g<<2)>>2]=n}}else{c[k>>2]=Bf(c[j>>2]|0,c[k>>2]|0,(c[l>>2]|0)-(c[p>>2]|0)|0,(c[m>>2]|0)-1|0,(c[p>>2]|0)+1|0,c[q>>2]|0)|0}c[p>>2]=(c[p>>2]|0)+1}if((s|0)==6){Ba(6232,4528,162,6216)}else if((s|0)==13){i=h;return c[k>>2]|0}return 0}function Cf(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0;f=i;i=i+32|0;g=f+28|0;h=f+24|0;j=f+20|0;k=f+16|0;l=f+12|0;m=f+8|0;n=f+4|0;o=f;c[h>>2]=b;c[j>>2]=d;c[k>>2]=e;c[l>>2]=c[c[h>>2]>>2];c[m>>2]=0;a:while(1){if((a[c[l>>2]|0]|0)==0){p=16;break}if((a[c[l>>2]|0]|0)==44){p=16;break}e=c[l>>2]|0;c[l>>2]=e+1;c[n>>2]=a[e]|0;e=c[n>>2]|0;if((c[n>>2]|0)>=97&(c[n>>2]|0)<=122){c[m>>2]=(c[m>>2]|0)+(e-97+1);continue}if((e|0)==95){continue}if(!((c[n>>2]|0)>48&(c[n>>2]|0)<=57)){p=15;break}c[o>>2]=Zf((c[l>>2]|0)+ -1|0)|0;if((c[o>>2]|0)<1){p=10;break}if((c[o>>2]|0)>(c[j>>2]|0)){p=10;break}c[m>>2]=(c[m>>2]|0)+1;while(1){if((a[c[l>>2]|0]|0)<48){continue a}if((a[c[l>>2]|0]|0)>57){continue a}c[l>>2]=(c[l>>2]|0)+1}}if((p|0)==10){c[g>>2]=6704;q=c[g>>2]|0;i=f;return q|0}else if((p|0)==15){c[g>>2]=5888;q=c[g>>2]|0;i=f;return q|0}else if((p|0)==16){if((c[m>>2]|0)<(c[k>>2]|0)){c[g>>2]=6744;q=c[g>>2]|0;i=f;return q|0}if((c[m>>2]|0)>(c[k>>2]|0)){c[g>>2]=6776;q=c[g>>2]|0;i=f;return q|0}else{c[c[h>>2]>>2]=c[l>>2];c[g>>2]=0;q=c[g>>2]|0;i=f;return q|0}}return 0}function Df(a,b,d,e,f,g,h){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;var j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0;j=i;i=i+64|0;k=j+60|0;l=j+56|0;m=j+52|0;n=j+48|0;o=j+44|0;p=j+40|0;q=j+36|0;r=j+32|0;s=j+28|0;t=j+24|0;u=j+20|0;v=j+16|0;w=j+12|0;x=j+8|0;y=j+4|0;z=j;c[l>>2]=a;c[m>>2]=b;c[n>>2]=d;c[o>>2]=e;c[p>>2]=f;c[q>>2]=g;c[r>>2]=h;c[s>>2]=yf(c[l>>2]|0,t,c[m>>2]|0,c[n>>2]|0)|0;if((c[s>>2]|0)!=0){c[k>>2]=c[s>>2];A=c[k>>2]|0;i=j;return A|0}do{if((c[q>>2]|0)==(c[r>>2]|0)){if((c[o>>2]|0)!=(c[p>>2]|0)){Ba(6472,4528,3933,6504)}s=Z(c[o>>2]|0,c[q>>2]|0)|0;if((s|0)==(c[n>>2]|0)){break}else{Ba(6528,4528,3934,6504)}}}while(0);c[z>>2]=0;c[u>>2]=sd(c[p>>2]<<2)|0;c[v>>2]=sd(c[p>>2]<<2)|0;c[w>>2]=0;while(1){if((c[w>>2]|0)>=(c[n>>2]|0)){B=22;break}c[x>>2]=Ac(c[t>>2]|0,c[w>>2]|0)|0;c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[z>>2]|0)){break}C=c[y>>2]|0;if((c[(c[u>>2]|0)+(c[y>>2]<<2)>>2]|0)==(c[x>>2]|0)){B=14;break}c[y>>2]=C+1}if((B|0)==14?(B=0,s=(c[v>>2]|0)+(C<<2)|0,c[s>>2]=(c[s>>2]|0)+1,(c[(c[v>>2]|0)+(c[y>>2]<<2)>>2]|0)>(c[r>>2]|0)):0){B=15;break}if((c[y>>2]|0)==(c[z>>2]|0)){if((c[z>>2]|0)>=(c[p>>2]|0)){B=19;break}c[(c[u>>2]|0)+(c[z>>2]<<2)>>2]=c[x>>2];c[(c[v>>2]|0)+(c[z>>2]<<2)>>2]=1;c[z>>2]=(c[z>>2]|0)+1}c[w>>2]=(c[w>>2]|0)+1}if((B|0)==15){td(c[t>>2]|0);td(c[u>>2]|0);td(c[v>>2]|0);c[k>>2]=6568;A=c[k>>2]|0;i=j;return A|0}else if((B|0)==19){td(c[t>>2]|0);td(c[u>>2]|0);td(c[v>>2]|0);c[k>>2]=6600;A=c[k>>2]|0;i=j;return A|0}else if((B|0)==22){if((c[z>>2]|0)<(c[o>>2]|0)){td(c[t>>2]|0);td(c[u>>2]|0);td(c[v>>2]|0);c[k>>2]=6632;A=c[k>>2]|0;i=j;return A|0}c[y>>2]=0;while(1){if((c[y>>2]|0)>=(c[z>>2]|0)){B=29;break}if((c[(c[v>>2]|0)+(c[y>>2]<<2)>>2]|0)<(c[q>>2]|0)){B=27;break}c[y>>2]=(c[y>>2]|0)+1}if((B|0)==27){td(c[t>>2]|0);td(c[u>>2]|0);td(c[v>>2]|0);c[k>>2]=6672;A=c[k>>2]|0;i=j;return A|0}else if((B|0)==29){td(c[u>>2]|0);td(c[v>>2]|0);td(c[t>>2]|0);c[k>>2]=0;A=c[k>>2]|0;i=j;return A|0}}return 0}function Ef(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0;e=i;i=i+80|0;f=e+68|0;g=e+64|0;h=e+60|0;j=e+56|0;k=e+52|0;l=e+48|0;m=e+44|0;n=e+40|0;o=e+36|0;p=e+32|0;q=e+28|0;r=e+24|0;s=e+20|0;t=e+16|0;u=e+12|0;v=e+8|0;w=e+4|0;x=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;c[m>>2]=Z(c[f>>2]|0,c[f>>2]|0)|0;c[n>>2]=0;c[o>>2]=hf(1,c[f>>2]|0,c[m>>2]|0,c[f>>2]|0,c[m>>2]|0)|0;c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[m>>2]|0)){break}c[(c[(c[o>>2]|0)+16>>2]|0)+(c[k>>2]<<2)>>2]=-1;c[k>>2]=(c[k>>2]|0)+1}c[j>>2]=0;c[l>>2]=0;while(1){if((c[l>>2]|0)>=(c[f>>2]|0)){break}c[k>>2]=0;while(1){y=c[l>>2]|0;if((c[k>>2]|0)>=(c[f>>2]|0)){break}d=Z(y,c[f>>2]|0)|0;c[q>>2]=d+(c[k>>2]|0);if(!((c[(c[(c[o>>2]|0)+16>>2]|0)+(c[q>>2]<<2)>>2]|0)!=-1)){c[(c[(c[o>>2]|0)+16>>2]|0)+(c[q>>2]<<2)>>2]=c[j>>2];c[p>>2]=pe(c[g>>2]|0,4)|0;do{if(((c[q>>2]|0)+1|0)<(c[m>>2]|0)){if((c[p>>2]|0)<4){if((c[h>>2]|0)!=0){z=21;break}if((c[p>>2]|0)<1){z=21;break}}c[r>>2]=(c[q>>2]|0)+1;if(((c[k>>2]|0)+1|0)!=(c[f>>2]|0)?!((c[(c[(c[o>>2]|0)+16>>2]|0)+(c[r>>2]<<2)>>2]|0)!=-1):0){if(((c[q>>2]|0)+(c[f>>2]|0)|0)<(c[m>>2]|0)?(pe(c[g>>2]|0,1)|0)==0:0){z=17}}else{z=17}if((z|0)==17){z=0;c[r>>2]=(c[q>>2]|0)+(c[f>>2]|0)}if((c[r>>2]|0)>=(c[m>>2]|0)){c[n>>2]=(c[n>>2]|0)+1;break}else{c[(c[(c[o>>2]|0)+16>>2]|0)+(c[r>>2]<<2)>>2]=c[j>>2];break}}else{z=21}}while(0);if((z|0)==21){z=0;c[n>>2]=(c[n>>2]|0)+1}c[j>>2]=(c[j>>2]|0)+1}c[k>>2]=(c[k>>2]|0)+1}c[l>>2]=y+1}c[(c[o>>2]|0)+32>>2]=c[j>>2];Af(c[o>>2]|0);c[l>>2]=0;c[k>>2]=0;while(1){if((c[k>>2]|0)>=(c[(c[o>>2]|0)+32>>2]|0)){break}if((c[(c[(c[o>>2]|0)+24>>2]|0)+(c[k>>2]<<2)>>2]|0)==1){c[l>>2]=(c[l>>2]|0)+1}c[k>>2]=(c[k>>2]|0)+1}if((c[l>>2]|0)!=(c[n>>2]|0)){Ba(6960,4528,3519,6984)}if((c[n>>2]|0)<=0){A=c[o>>2]|0;i=e;return A|0}if((c[h>>2]|0)==0){A=c[o>>2]|0;i=e;return A|0}c[s>>2]=0;while(1){if((c[s>>2]|0)>=(c[(c[o>>2]|0)+32>>2]|0)){break}h=c[s>>2]|0;if((c[(c[(c[o>>2]|0)+24>>2]|0)+(c[s>>2]<<2)>>2]|0)>1){c[s>>2]=h+1;continue}c[t>>2]=c[c[(c[(c[o>>2]|0)+20>>2]|0)+(h<<2)>>2]>>2];c[u>>2]=(c[t>>2]|0)%(c[f>>2]|0)|0;c[v>>2]=(c[t>>2]|0)/(c[f>>2]|0)|0;a:do{if(((c[t>>2]|0)+1|0)==(c[m>>2]|0)){c[w>>2]=(c[t>>2]|0)-1}else{do{if(((c[u>>2]|0)+1|0)<(c[f>>2]|0)){if(((c[v>>2]|0)+1|0)!=(c[f>>2]|0)?(pe(c[g>>2]|0,1)|0)!=0:0){break}c[w>>2]=(c[t>>2]|0)+1;break a}}while(0);c[w>>2]=(c[t>>2]|0)+(c[f>>2]|0)}}while(0);c[x>>2]=c[(c[(c[o>>2]|0)+16>>2]|0)+(c[w>>2]<<2)>>2];if((c[(c[(c[o>>2]|0)+24>>2]|0)+(c[x>>2]<<2)>>2]|0)==1){c[n>>2]=(c[n>>2]|0)+ -1}c[n>>2]=(c[n>>2]|0)+ -1;Of(c[o>>2]|0,c[s>>2]|0,c[x>>2]|0);if((c[s>>2]|0)>=(c[x>>2]|0)){continue}c[s>>2]=(c[s>>2]|0)+1}if((c[n>>2]|0)!=0){Ba(7008,4528,3547,6984)}A=c[o>>2]|0;i=e;return A|0}function Ff(b,d,e,f,g,h,j){b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;j=j|0;var k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0;k=i;i=i+48|0;l=k+40|0;m=k+36|0;n=k+32|0;o=k+28|0;p=k+24|0;q=k+20|0;r=k+16|0;s=k+12|0;t=k+8|0;u=k+4|0;v=k;c[l>>2]=b;c[m>>2]=d;c[n>>2]=e;c[o>>2]=f;c[p>>2]=g;c[q>>2]=h;c[r>>2]=j;cg(c[p>>2]|0,0,Z(c[l>>2]|0,c[l>>2]|0)|0)|0;c[s>>2]=sd(48)|0;c[c[s>>2]>>2]=c[l>>2];c[(c[s>>2]|0)+4>>2]=c[m>>2];c[(c[s>>2]|0)+12>>2]=c[p>>2];m=sd(c[l>>2]<<2)|0;c[(c[s>>2]|0)+16>>2]=m;m=sd(c[l>>2]<<2)|0;c[(c[s>>2]|0)+20>>2]=m;m=sd(c[l>>2]<<2)|0;c[(c[s>>2]|0)+24>>2]=m;if((c[n>>2]|0)!=0){c[(c[s>>2]|0)+8>>2]=c[n>>2];m=sd(c[(c[(c[s>>2]|0)+8>>2]|0)+32>>2]<<2)|0;c[(c[s>>2]|0)+28>>2]=m;cg(c[(c[s>>2]|0)+28>>2]|0,0,c[(c[n>>2]|0)+32>>2]<<2|0)|0}else{c[(c[s>>2]|0)+28>>2]=0}cg(c[(c[s>>2]|0)+16>>2]|0,0,c[l>>2]<<2|0)|0;cg(c[(c[s>>2]|0)+20>>2]|0,0,c[l>>2]<<2|0)|0;cg(c[(c[s>>2]|0)+24>>2]|0,0,c[l>>2]<<2|0)|0;if((c[o>>2]|0)!=0){o=sd(8)|0;c[(c[s>>2]|0)+32>>2]=o;o=c[(c[s>>2]|0)+32>>2]|0;c[o+0>>2]=0;c[o+4>>2]=0}else{c[(c[s>>2]|0)+32>>2]=0}c[t>>2]=0;while(1){if((c[t>>2]|0)>=(c[l>>2]|0)){break}a[(c[p>>2]|0)+(c[t>>2]|0)|0]=(c[t>>2]|0)+1;c[t>>2]=(c[t>>2]|0)+1}ee(c[p>>2]|0,c[l>>2]|0,1,c[q>>2]|0);c[t>>2]=0;while(1){if((c[t>>2]|0)>=(c[l>>2]|0)){break}Pf(c[s>>2]|0,c[t>>2]|0,0,a[(c[p>>2]|0)+(c[t>>2]|0)|0]|0);c[t>>2]=(c[t>>2]|0)+1}o=sd((Z(c[l>>2]|0,c[l>>2]|0)|0)*12|0)|0;c[(c[s>>2]|0)+36>>2]=o;c[(c[s>>2]|0)+40>>2]=0;c[(c[s>>2]|0)+44>>2]=c[q>>2];c[u>>2]=1;while(1){if((c[u>>2]|0)>=(c[l>>2]|0)){break}c[t>>2]=0;while(1){if((c[t>>2]|0)>=(c[l>>2]|0)){break}c[(c[(c[s>>2]|0)+36>>2]|0)+((c[(c[s>>2]|0)+40>>2]|0)*12|0)>>2]=c[t>>2];c[(c[(c[s>>2]|0)+36>>2]|0)+((c[(c[s>>2]|0)+40>>2]|0)*12|0)+4>>2]=c[u>>2];o=pe(c[q>>2]|0,31)|0;c[(c[(c[s>>2]|0)+36>>2]|0)+((c[(c[s>>2]|0)+40>>2]|0)*12|0)+8>>2]=o;o=(c[s>>2]|0)+40|0;c[o>>2]=(c[o>>2]|0)+1;c[t>>2]=(c[t>>2]|0)+1}c[u>>2]=(c[u>>2]|0)+1}c[v>>2]=Qf(c[s>>2]|0,c[p>>2]|0,r)|0;td(c[(c[s>>2]|0)+36>>2]|0);td(c[(c[s>>2]|0)+28>>2]|0);td(c[(c[s>>2]|0)+24>>2]|0);td(c[(c[s>>2]|0)+20>>2]|0);td(c[(c[s>>2]|0)+16>>2]|0);td(c[s>>2]|0);i=k;return c[v>>2]|0}function Gf(b,e,f,g){b=b|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0;h=i;i=i+32|0;j=h+24|0;k=h+20|0;l=h+16|0;m=h+12|0;n=h+8|0;o=h+4|0;p=h;c[j>>2]=b;c[k>>2]=e;c[l>>2]=f;c[m>>2]=g;cg(c[k>>2]|0,0,c[m>>2]|0)|0;c[n>>2]=0;while(1){if((c[n>>2]|0)>=(c[(c[j>>2]|0)+32>>2]|0)){q=15;break}c[p>>2]=0;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[m>>2]|0)){break}if((c[(c[(c[j>>2]|0)+16>>2]|0)+(c[o>>2]<<2)>>2]|0)==(c[n>>2]|0)){c[p>>2]=(c[p>>2]|0)+(d[(c[l>>2]|0)+(c[o>>2]|0)|0]|0)}c[o>>2]=(c[o>>2]|0)+1}c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[m>>2]|0)){break}if((c[(c[(c[j>>2]|0)+16>>2]|0)+(c[o>>2]<<2)>>2]|0)==(c[n>>2]|0)){break}c[o>>2]=(c[o>>2]|0)+1}if((c[o>>2]|0)==(c[m>>2]|0)){q=13;break}a[(c[k>>2]|0)+(c[o>>2]|0)|0]=c[p>>2];c[n>>2]=(c[n>>2]|0)+1}if((q|0)==13){Ba(6928,4528,3474,6944)}else if((q|0)==15){i=h;return}}function Hf(a,b,e,f,g){a=a|0;b=b|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0;h=i;i=i+80|0;j=h+64|0;k=h+60|0;l=h+56|0;m=h+48|0;n=h+44|0;o=h+40|0;p=h+36|0;q=h+32|0;r=h+28|0;s=h+24|0;t=h+20|0;u=h+16|0;v=h+12|0;w=h+8|0;x=h+4|0;y=h;c[k>>2]=a;c[l>>2]=b;c[h+52>>2]=e;c[m>>2]=f;c[n>>2]=g;c[r>>2]=sd((Z(c[(c[k>>2]|0)+32>>2]|0,c[(c[k>>2]|0)+32>>2]|0)|0)<<3)|0;c[s>>2]=0;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[(c[k>>2]|0)+32>>2]|0)){break}c[p>>2]=(c[o>>2]|0)+1;while(1){z=c[o>>2]|0;if((c[p>>2]|0)>=(c[(c[k>>2]|0)+32>>2]|0)){break}a:do{if(((c[(c[(c[k>>2]|0)+24>>2]|0)+(z<<2)>>2]|0)+(c[(c[(c[k>>2]|0)+24>>2]|0)+(c[p>>2]<<2)>>2]|0)|0)<=(c[(c[k>>2]|0)+36>>2]|0)){c[q>>2]=0;while(1){if((c[q>>2]|0)>=(c[(c[(c[k>>2]|0)+24>>2]|0)+(c[o>>2]<<2)>>2]|0)){break a}c[t>>2]=c[(c[(c[(c[k>>2]|0)+20>>2]|0)+(c[o>>2]<<2)>>2]|0)+(c[q>>2]<<2)>>2];c[u>>2]=(c[t>>2]|0)/(c[l>>2]|0)|0;c[v>>2]=(c[t>>2]|0)%(c[l>>2]|0)|0;if((c[u>>2]|0)>0?(c[(c[(c[k>>2]|0)+16>>2]|0)+((c[t>>2]|0)-(c[l>>2]|0)<<2)>>2]|0)==(c[p>>2]|0):0){break}if(((c[u>>2]|0)+1|0)<(c[l>>2]|0)?(c[(c[(c[k>>2]|0)+16>>2]|0)+((c[t>>2]|0)+(c[l>>2]|0)<<2)>>2]|0)==(c[p>>2]|0):0){break}if((c[v>>2]|0)>0?(c[(c[(c[k>>2]|0)+16>>2]|0)+((c[t>>2]|0)-1<<2)>>2]|0)==(c[p>>2]|0):0){break}if(((c[v>>2]|0)+1|0)<(c[l>>2]|0)?(c[(c[(c[k>>2]|0)+16>>2]|0)+((c[t>>2]|0)+1<<2)>>2]|0)==(c[p>>2]|0):0){break}c[q>>2]=(c[q>>2]|0)+1}c[(c[r>>2]|0)+(c[s>>2]<<3)>>2]=c[o>>2];c[(c[r>>2]|0)+(c[s>>2]<<3)+4>>2]=c[p>>2]}}while(0);c[p>>2]=(c[p>>2]|0)+1}c[o>>2]=z+1}while(1){if((c[s>>2]|0)<=0){A=32;break}c[o>>2]=qe(c[n>>2]|0,c[s>>2]|0)|0;c[w>>2]=c[(c[r>>2]|0)+(c[o>>2]<<3)>>2];c[x>>2]=c[(c[r>>2]|0)+(c[o>>2]<<3)+4>>2];if((c[o>>2]|0)!=((c[s>>2]|0)-1|0)){z=(c[r>>2]|0)+(c[o>>2]<<3)|0;p=(c[r>>2]|0)+((c[s>>2]|0)-1<<3)|0;c[z+0>>2]=c[p+0>>2];c[z+4>>2]=c[p+4>>2]}c[s>>2]=(c[s>>2]|0)+ -1;c[y>>2]=0;c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[(c[(c[k>>2]|0)+24>>2]|0)+(c[w>>2]<<2)>>2]|0)){break}c[y>>2]=c[y>>2]|1<<(d[(c[m>>2]|0)+(c[(c[(c[(c[k>>2]|0)+20>>2]|0)+(c[w>>2]<<2)>>2]|0)+(c[o>>2]<<2)>>2]|0)|0]|0);c[o>>2]=(c[o>>2]|0)+1}c[o>>2]=0;while(1){if((c[o>>2]|0)>=(c[(c[(c[k>>2]|0)+24>>2]|0)+(c[x>>2]<<2)>>2]|0)){break}if((c[y>>2]&1<<(d[(c[m>>2]|0)+(c[(c[(c[(c[k>>2]|0)+20>>2]|0)+(c[x>>2]<<2)>>2]|0)+(c[o>>2]<<2)>>2]|0)|0]|0)|0)!=0){break}c[o>>2]=(c[o>>2]|0)+1}if((c[o>>2]|0)==(c[(c[(c[k>>2]|0)+24>>2]|0)+(c[x>>2]<<2)>>2]|0)){A=31;break}}if((A|0)==31){Of(c[k>>2]|0,c[w>>2]|0,c[x>>2]|0);td(c[r>>2]|0);c[j>>2]=1;B=c[j>>2]|0;i=h;return B|0}else if((A|0)==32){td(c[r>>2]|0);c[j>>2]=0;B=c[j>>2]|0;i=h;return B|0}return 0}function If(a,b,d,e,f){a=a|0;b=b|0;d=d|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;g=i;i=i+48|0;h=g+32|0;j=g+28|0;k=g+24|0;l=g+20|0;m=g+16|0;n=g+12|0;o=g+8|0;p=g+4|0;q=g;c[h>>2]=a;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=c[c[h>>2]>>2];c[o>>2]=c[(c[h>>2]|0)+4>>2];c[p>>2]=Z(c[n>>2]|0,c[o>>2]|0)|0;c[q>>2]=0;o=c[j>>2]|0;n=c[l>>2]|0;c[l>>2]=n+4;c[n>>2]=o;o=c[k>>2]|0;n=c[l>>2]|0;c[l>>2]=n+4;c[n>>2]=o;c[q>>2]=(c[q>>2]|0)+1;switch(c[m>>2]|0){case 6:{m=c[k>>2]|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=c[j>>2]|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;m=(c[p>>2]|0)-1-(c[j>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=(c[p>>2]|0)-1-(c[k>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;m=(c[p>>2]|0)-1-(c[k>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=(c[p>>2]|0)-1-(c[j>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;r=c[q>>2]|0;i=g;return r|0};case 1:{m=(c[p>>2]|0)-1-(c[j>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=(c[p>>2]|0)-1-(c[k>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;r=c[q>>2]|0;i=g;return r|0};case 3:{m=(c[p>>2]|0)-1-(c[j>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=c[k>>2]|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;r=c[q>>2]|0;i=g;return r|0};case 7:{m=(c[p>>2]|0)-1-(c[j>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=c[k>>2]|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;m=c[j>>2]|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=(c[p>>2]|0)-1-(c[k>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;m=(c[p>>2]|0)-1-(c[j>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=(c[p>>2]|0)-1-(c[k>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;m=c[k>>2]|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=c[j>>2]|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;m=c[k>>2]|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=(c[p>>2]|0)-1-(c[j>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;m=(c[p>>2]|0)-1-(c[k>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=c[j>>2]|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;m=(c[p>>2]|0)-1-(c[k>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=(c[p>>2]|0)-1-(c[j>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;r=c[q>>2]|0;i=g;return r|0};case 5:{m=(c[p>>2]|0)-1-(c[j>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=c[k>>2]|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;m=c[j>>2]|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=(c[p>>2]|0)-1-(c[k>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;m=(c[p>>2]|0)-1-(c[j>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=(c[p>>2]|0)-1-(c[k>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;r=c[q>>2]|0;i=g;return r|0};case 2:{m=(c[p>>2]|0)-1-(c[k>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=c[j>>2]|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;m=c[k>>2]|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=(c[p>>2]|0)-1-(c[j>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;c[q>>2]=(c[q>>2]|0)+1;m=(c[p>>2]|0)-1-(c[j>>2]|0)|0;o=c[l>>2]|0;c[l>>2]=o+4;c[o>>2]=m;m=(c[p>>2]|0)-1-(c[k>>2]|0)|0;p=c[l>>2]|0;c[l>>2]=p+4;c[p>>2]=m;c[q>>2]=(c[q>>2]|0)+1;r=c[q>>2]|0;i=g;return r|0};case 4:{m=c[k>>2]|0;k=c[l>>2]|0;c[l>>2]=k+4;c[k>>2]=m;m=c[j>>2]|0;j=c[l>>2]|0;c[l>>2]=j+4;c[j>>2]=m;c[q>>2]=(c[q>>2]|0)+1;r=c[q>>2]|0;i=g;return r|0};default:{r=c[q>>2]|0;i=g;return r|0}}return 0}function Jf(b,d,e,f,g){b=b|0;d=d|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0;h=i;i=i+48|0;j=h+44|0;k=h+40|0;l=h+36|0;m=h+32|0;n=h+28|0;o=h+24|0;p=h+20|0;q=h+16|0;r=h+12|0;s=h+8|0;t=h+4|0;u=h;c[j>>2]=b;c[k>>2]=d;c[l>>2]=e;c[m>>2]=f;c[n>>2]=g;c[o>>2]=c[c[j>>2]>>2];c[p>>2]=c[(c[j>>2]|0)+4>>2];c[q>>2]=Z(c[o>>2]|0,c[p>>2]|0)|0;c[r>>2]=Z(c[q>>2]|0,c[q>>2]|0)|0;c[u>>2]=(Kf(c[r>>2]|0)|0)+1;if((c[p>>2]|0)==1){q=(Lf(c[l>>2]|0)|0)+1|0;c[u>>2]=(c[u>>2]|0)+q}if((c[(c[j>>2]|0)+24>>2]|0)!=0){q=(Lf(c[n>>2]|0)|0)+1|0;c[u>>2]=(c[u>>2]|0)+q;q=(Kf(c[r>>2]|0)|0)+1|0;c[u>>2]=(c[u>>2]|0)+q}c[t>>2]=sd(c[u>>2]|0)|0;c[s>>2]=Mf(c[t>>2]|0,c[k>>2]|0,c[r>>2]|0)|0;if((c[p>>2]|0)==1){p=c[s>>2]|0;c[s>>2]=p+1;a[p]=44;c[s>>2]=Nf(c[s>>2]|0,c[l>>2]|0)|0}if((c[(c[j>>2]|0)+24>>2]|0)!=0){j=c[s>>2]|0;c[s>>2]=j+1;a[j]=44;c[s>>2]=Nf(c[s>>2]|0,c[n>>2]|0)|0;n=c[s>>2]|0;c[s>>2]=n+1;a[n]=44;c[s>>2]=Mf(c[s>>2]|0,c[m>>2]|0,c[r>>2]|0)|0}if(((c[s>>2]|0)-(c[t>>2]|0)|0)<(c[u>>2]|0)){u=c[s>>2]|0;c[s>>2]=u+1;a[u]=0;c[t>>2]=ud(c[t>>2]|0,(c[s>>2]|0)-(c[t>>2]|0)|0)|0;i=h;return c[t>>2]|0}else{Ba(6880,4528,3339,6904)}return 0}function Kf(a){a=a|0;var b=0,d=0,e=0,f=0,g=0;b=i;i=i+16|0;d=b+8|0;e=b+4|0;f=b;c[d>>2]=a;c[f>>2]=1;c[e>>2]=c[d>>2];while(1){g=c[f>>2]|0;if((c[e>>2]|0)<=26){break}c[f>>2]=g+1;c[e>>2]=(c[e>>2]|0)-26}e=Z(g,c[d>>2]|0)|0;i=b;return e|0}function Lf(a){a=a|0;var b=0,d=0,e=0,f=0;b=i;i=i+16|0;d=b+8|0;e=b+4|0;f=b;c[d>>2]=a;c[e>>2]=Z(c[(c[d>>2]|0)+4>>2]|0,c[(c[d>>2]|0)+8>>2]|0)|0;c[f>>2]=Z(c[e>>2]|0,c[e>>2]|0)|0;e=Kf(c[f>>2]|0)|0;i=b;return e|0}function Mf(b,e,f){b=b|0;e=e|0;f=f|0;var g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;g=i;i=i+48|0;h=g;j=g+32|0;k=g+28|0;l=g+24|0;m=g+20|0;n=g+16|0;o=g+12|0;p=g+8|0;q=g+4|0;c[j>>2]=b;c[k>>2]=e;c[l>>2]=f;c[o>>2]=c[j>>2];c[m>>2]=0;c[n>>2]=0;while(1){if((c[n>>2]|0)>(c[l>>2]|0)){break}if((c[n>>2]|0)<(c[l>>2]|0)){r=d[(c[k>>2]|0)+(c[n>>2]|0)|0]|0}else{r=-1}c[p>>2]=r;f=c[m>>2]|0;if((c[p>>2]|0)!=0){a:do{if((f|0)==0){if((c[o>>2]|0)>>>0>(c[j>>2]|0)>>>0?(c[p>>2]|0)>0:0){e=c[o>>2]|0;c[o>>2]=e+1;a[e]=95}}else{while(1){if((c[m>>2]|0)<=0){break a}e=96+(c[m>>2]|0)|0;c[q>>2]=e;c[q>>2]=(c[m>>2]|0)>26?122:e;e=c[q>>2]&255;b=c[o>>2]|0;c[o>>2]=b+1;a[b]=e;c[m>>2]=(c[m>>2]|0)-((c[q>>2]|0)-96)}}}while(0);if((c[p>>2]|0)>0){e=c[o>>2]|0;c[h>>2]=c[p>>2];b=ab(e|0,4512,h|0)|0;c[o>>2]=(c[o>>2]|0)+b}c[m>>2]=0}else{c[m>>2]=f+1}c[n>>2]=(c[n>>2]|0)+1}i=g;return c[o>>2]|0}function Nf(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;e=i;i=i+48|0;f=e+44|0;g=e+40|0;h=e+36|0;j=e+32|0;k=e+28|0;l=e+24|0;m=e+20|0;n=e+16|0;o=e+12|0;p=e+8|0;q=e+4|0;r=e;c[f>>2]=b;c[g>>2]=d;c[j>>2]=0;c[k>>2]=c[(c[g>>2]|0)+4>>2];c[l>>2]=c[(c[g>>2]|0)+8>>2];c[m>>2]=Z(c[k>>2]|0,c[l>>2]|0)|0;c[h>>2]=0;while(1){if((c[h>>2]|0)>(Z(c[m>>2]<<1,(c[m>>2]|0)-1|0)|0)){break}if((c[h>>2]|0)==(Z(c[m>>2]<<1,(c[m>>2]|0)-1|0)|0)){c[r>>2]=1}else{l=(c[h>>2]|0)<(Z(c[m>>2]|0,(c[m>>2]|0)-1|0)|0);k=(c[h>>2]|0)/((c[m>>2]|0)-1|0)|0;if(l){c[o>>2]=k;c[n>>2]=(c[h>>2]|0)%((c[m>>2]|0)-1|0)|0;l=Z(c[o>>2]|0,c[m>>2]|0)|0;c[p>>2]=l+(c[n>>2]|0);l=Z(c[o>>2]|0,c[m>>2]|0)|0;c[q>>2]=l+(c[n>>2]|0)+1}else{c[n>>2]=k-(c[m>>2]|0);c[o>>2]=(c[h>>2]|0)%((c[m>>2]|0)-1|0)|0;k=Z(c[o>>2]|0,c[m>>2]|0)|0;c[p>>2]=k+(c[n>>2]|0);k=Z((c[o>>2]|0)+1|0,c[m>>2]|0)|0;c[q>>2]=k+(c[n>>2]|0)}c[r>>2]=(c[(c[(c[g>>2]|0)+16>>2]|0)+(c[p>>2]<<2)>>2]|0)!=(c[(c[(c[g>>2]|0)+16>>2]|0)+(c[q>>2]<<2)>>2]|0)}if((c[r>>2]|0)!=0){while(1){if((c[j>>2]|0)<=25){break}k=c[f>>2]|0;c[f>>2]=k+1;a[k]=122;c[j>>2]=(c[j>>2]|0)-25}if((c[j>>2]|0)!=0){k=96+(c[j>>2]|0)&255;l=c[f>>2]|0;c[f>>2]=l+1;a[l]=k}else{k=c[f>>2]|0;c[f>>2]=k+1;a[k]=95}c[j>>2]=0}else{c[j>>2]=(c[j>>2]|0)+1}c[h>>2]=(c[h>>2]|0)+1}i=e;return c[f>>2]|0}function Of(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;e=i;i=i+32|0;f=e+16|0;g=e+12|0;h=e+8|0;j=e+4|0;k=e;c[f>>2]=a;c[g>>2]=b;c[h>>2]=d;if((c[h>>2]|0)<(c[g>>2]|0)){c[k>>2]=c[h>>2];c[h>>2]=c[g>>2];c[g>>2]=c[k>>2]}c[j>>2]=0;while(1){l=c[g>>2]|0;if((c[j>>2]|0)>=(c[(c[(c[f>>2]|0)+24>>2]|0)+(c[h>>2]<<2)>>2]|0)){break}c[(c[(c[f>>2]|0)+16>>2]|0)+(c[(c[(c[(c[f>>2]|0)+20>>2]|0)+(c[h>>2]<<2)>>2]|0)+(c[j>>2]<<2)>>2]<<2)>>2]=l;c[j>>2]=(c[j>>2]|0)+1}eg((c[(c[(c[f>>2]|0)+20>>2]|0)+(l<<2)>>2]|0)+(c[(c[(c[f>>2]|0)+24>>2]|0)+(c[g>>2]<<2)>>2]<<2)|0,c[(c[(c[f>>2]|0)+20>>2]|0)+(c[h>>2]<<2)>>2]|0,c[(c[(c[f>>2]|0)+24>>2]|0)+(c[h>>2]<<2)>>2]<<2|0)|0;l=(c[(c[f>>2]|0)+24>>2]|0)+(c[g>>2]<<2)|0;c[l>>2]=(c[l>>2]|0)+(c[(c[(c[f>>2]|0)+24>>2]|0)+(c[h>>2]<<2)>>2]|0);c[g>>2]=(c[(c[f>>2]|0)+32>>2]|0)-1;if((c[h>>2]|0)==(c[g>>2]|0)){m=c[g>>2]|0;n=c[f>>2]|0;o=n+32|0;c[o>>2]=m;i=e;return}eg(c[(c[(c[f>>2]|0)+20>>2]|0)+(c[h>>2]<<2)>>2]|0,c[(c[(c[f>>2]|0)+20>>2]|0)+(c[g>>2]<<2)>>2]|0,c[(c[(c[f>>2]|0)+24>>2]|0)+(c[g>>2]<<2)>>2]<<2|0)|0;c[j>>2]=0;while(1){if((c[j>>2]|0)>=(c[(c[(c[f>>2]|0)+24>>2]|0)+(c[g>>2]<<2)>>2]|0)){break}c[(c[(c[f>>2]|0)+16>>2]|0)+(c[(c[(c[(c[f>>2]|0)+20>>2]|0)+(c[g>>2]<<2)>>2]|0)+(c[j>>2]<<2)>>2]<<2)>>2]=c[h>>2];c[j>>2]=(c[j>>2]|0)+1}c[(c[(c[f>>2]|0)+24>>2]|0)+(c[h>>2]<<2)>>2]=c[(c[(c[f>>2]|0)+24>>2]|0)+(c[g>>2]<<2)>>2];m=c[g>>2]|0;n=c[f>>2]|0;o=n+32|0;c[o>>2]=m;i=e;return}function Pf(b,e,f,g){b=b|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0;h=i;i=i+32|0;j=h+16|0;k=h+12|0;l=h+8|0;m=h+20|0;n=h+4|0;o=h;c[j>>2]=b;c[k>>2]=e;c[l>>2]=f;a[m]=g;c[n>>2]=1<<(d[m]|0);c[o>>2]=c[c[j>>2]>>2];g=(c[(c[j>>2]|0)+16>>2]|0)+(c[l>>2]<<2)|0;c[g>>2]=c[g>>2]|c[n>>2];g=(c[(c[j>>2]|0)+20>>2]|0)+(c[k>>2]<<2)|0;c[g>>2]=c[g>>2]|c[n>>2];g=Z(c[l>>2]|0,c[o>>2]|0)|0;f=(c[(c[j>>2]|0)+24>>2]|0)+(c[(c[(c[(c[j>>2]|0)+4>>2]|0)+16>>2]|0)+(g+(c[k>>2]|0)<<2)>>2]<<2)|0;c[f>>2]=c[f>>2]|c[n>>2];if((c[(c[j>>2]|0)+28>>2]|0)!=0){f=Z(c[l>>2]|0,c[o>>2]|0)|0;g=(c[(c[j>>2]|0)+28>>2]|0)+(c[(c[(c[(c[j>>2]|0)+8>>2]|0)+16>>2]|0)+(f+(c[k>>2]|0)<<2)>>2]<<2)|0;c[g>>2]=c[g>>2]|c[n>>2]}if((c[(c[j>>2]|0)+32>>2]|0)!=0){g=Z(c[l>>2]|0,c[o>>2]|0)|0;if(((g+(c[k>>2]|0)|0)%((c[o>>2]|0)+1|0)|0|0)==0){g=c[(c[j>>2]|0)+32>>2]|0;c[g>>2]=c[g>>2]|c[n>>2]}g=Z(c[l>>2]|0,c[o>>2]|0)|0;if((((g+(c[k>>2]|0)|0)%((c[o>>2]|0)-1|0)|0|0)==0?(g=Z(c[l>>2]|0,c[o>>2]|0)|0,(g+(c[k>>2]|0)|0)>0):0)?(g=Z(c[l>>2]|0,c[o>>2]|0)|0,(g+(c[k>>2]|0)|0)<((Z(c[o>>2]|0,c[o>>2]|0)|0)-1|0)):0){g=(c[(c[j>>2]|0)+32>>2]|0)+4|0;c[g>>2]=c[g>>2]|c[n>>2]}}n=Z(c[l>>2]|0,c[o>>2]|0)|0;a[(c[(c[j>>2]|0)+12>>2]|0)+(n+(c[k>>2]|0))|0]=a[m]|0;i=h;return}function Qf(a,b,d){a=a|0;b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0;e=i;i=i+96|0;f=e+92|0;g=e+88|0;h=e+84|0;j=e+80|0;k=e+76|0;l=e+72|0;m=e+68|0;n=e+64|0;o=e+60|0;p=e+56|0;q=e+52|0;r=e+48|0;s=e+44|0;t=e+40|0;u=e+36|0;v=e+32|0;w=e+28|0;x=e+24|0;y=e+20|0;z=e+16|0;A=e+4|0;B=e;c[g>>2]=a;c[h>>2]=b;c[j>>2]=d;c[k>>2]=c[c[g>>2]>>2];if((c[(c[g>>2]|0)+40>>2]|0)==0){c[f>>2]=1;C=c[f>>2]|0;i=e;return C|0}if((c[c[j>>2]>>2]|0)<=0){c[f>>2]=0;C=c[f>>2]|0;i=e;return C|0}d=c[j>>2]|0;c[d>>2]=(c[d>>2]|0)+ -1;c[q>>2]=(c[k>>2]|0)+1;c[r>>2]=0;c[u>>2]=-1;c[p>>2]=-1;c[o>>2]=-1;c[l>>2]=-1;c[m>>2]=0;while(1){if((c[m>>2]|0)>=(c[(c[g>>2]|0)+40>>2]|0)){break}c[v>>2]=c[(c[(c[g>>2]|0)+36>>2]|0)+((c[m>>2]|0)*12|0)>>2];c[w>>2]=c[(c[(c[g>>2]|0)+36>>2]|0)+((c[m>>2]|0)*12|0)+4>>2];d=Z(c[w>>2]|0,c[k>>2]|0)|0;c[y>>2]=c[(c[(c[(c[g>>2]|0)+4>>2]|0)+16>>2]|0)+(d+(c[v>>2]|0)<<2)>>2];c[x>>2]=c[(c[(c[g>>2]|0)+16>>2]|0)+(c[w>>2]<<2)>>2]|c[(c[(c[g>>2]|0)+20>>2]|0)+(c[v>>2]<<2)>>2]|c[(c[(c[g>>2]|0)+24>>2]|0)+(c[y>>2]<<2)>>2];if((c[(c[g>>2]|0)+28>>2]|0)!=0){d=Z(c[w>>2]|0,c[k>>2]|0)|0;c[x>>2]=c[x>>2]|c[(c[(c[g>>2]|0)+28>>2]|0)+(c[(c[(c[(c[g>>2]|0)+8>>2]|0)+16>>2]|0)+(d+(c[v>>2]|0)<<2)>>2]<<2)>>2]}if((c[(c[g>>2]|0)+28>>2]|0)!=0){d=Z(c[w>>2]|0,c[k>>2]|0)|0;c[x>>2]=c[x>>2]|c[(c[(c[g>>2]|0)+28>>2]|0)+(c[(c[(c[(c[g>>2]|0)+8>>2]|0)+16>>2]|0)+(d+(c[v>>2]|0)<<2)>>2]<<2)>>2]}if((c[(c[g>>2]|0)+32>>2]|0)!=0){d=Z(c[w>>2]|0,c[k>>2]|0)|0;if(((d+(c[v>>2]|0)|0)%((c[k>>2]|0)+1|0)|0|0)==0){c[x>>2]=c[x>>2]|c[c[(c[g>>2]|0)+32>>2]>>2]}d=Z(c[w>>2]|0,c[k>>2]|0)|0;if((((d+(c[v>>2]|0)|0)%((c[k>>2]|0)-1|0)|0|0)==0?(d=Z(c[w>>2]|0,c[k>>2]|0)|0,(d+(c[v>>2]|0)|0)>0):0)?(d=Z(c[w>>2]|0,c[k>>2]|0)|0,(d+(c[v>>2]|0)|0)<((Z(c[k>>2]|0,c[k>>2]|0)|0)-1|0)):0){c[x>>2]=c[x>>2]|c[(c[(c[g>>2]|0)+32>>2]|0)+4>>2]}}c[y>>2]=0;c[n>>2]=1;while(1){if((c[n>>2]|0)>(c[k>>2]|0)){break}c[z>>2]=1<<c[n>>2];if((c[x>>2]&c[z>>2]|0)==0){c[y>>2]=(c[y>>2]|0)+1}c[n>>2]=(c[n>>2]|0)+1}if((c[y>>2]|0)>=(c[q>>2]|0)){if((c[y>>2]|0)==(c[q>>2]|0)?(c[(c[(c[g>>2]|0)+36>>2]|0)+((c[m>>2]|0)*12|0)+8>>2]|0)<(c[r>>2]|0):0){D=26}}else{D=26}if((D|0)==26){D=0;c[q>>2]=c[y>>2];c[r>>2]=c[(c[(c[g>>2]|0)+36>>2]|0)+((c[m>>2]|0)*12|0)+8>>2];c[o>>2]=c[v>>2];c[p>>2]=c[w>>2];c[l>>2]=c[m>>2];c[u>>2]=c[x>>2]}c[m>>2]=(c[m>>2]|0)+1}if((c[l>>2]|0)!=((c[(c[g>>2]|0)+40>>2]|0)-1|0)){x=(c[(c[g>>2]|0)+36>>2]|0)+(((c[(c[g>>2]|0)+40>>2]|0)-1|0)*12|0)|0;c[A+0>>2]=c[x+0>>2];c[A+4>>2]=c[x+4>>2];c[A+8>>2]=c[x+8>>2];x=(c[(c[g>>2]|0)+36>>2]|0)+(((c[(c[g>>2]|0)+40>>2]|0)-1|0)*12|0)|0;w=(c[(c[g>>2]|0)+36>>2]|0)+((c[l>>2]|0)*12|0)|0;c[x+0>>2]=c[w+0>>2];c[x+4>>2]=c[w+4>>2];c[x+8>>2]=c[w+8>>2];w=(c[(c[g>>2]|0)+36>>2]|0)+((c[l>>2]|0)*12|0)|0;c[w+0>>2]=c[A+0>>2];c[w+4>>2]=c[A+4>>2];c[w+8>>2]=c[A+8>>2]}c[t>>2]=sd(c[q>>2]<<2)|0;c[m>>2]=0;c[n>>2]=1;while(1){if((c[n>>2]|0)>(c[k>>2]|0)){break}c[B>>2]=1<<c[n>>2];if((c[u>>2]&c[B>>2]|0)==0){q=c[n>>2]|0;A=c[m>>2]|0;c[m>>2]=A+1;c[(c[t>>2]|0)+(A<<2)>>2]=q}c[n>>2]=(c[n>>2]|0)+1}if((c[(c[g>>2]|0)+44>>2]|0)!=0){ee(c[t>>2]|0,c[m>>2]|0,4,c[(c[g>>2]|0)+44>>2]|0)}c[s>>2]=0;c[l>>2]=0;while(1){if((c[l>>2]|0)>=(c[m>>2]|0)){break}c[n>>2]=c[(c[t>>2]|0)+(c[l>>2]<<2)>>2];Pf(c[g>>2]|0,c[o>>2]|0,c[p>>2]|0,c[n>>2]&255);B=(c[g>>2]|0)+40|0;c[B>>2]=(c[B>>2]|0)+ -1;if((Qf(c[g>>2]|0,c[h>>2]|0,c[j>>2]|0)|0)!=0){D=40;break}Rf(c[g>>2]|0,c[o>>2]|0,c[p>>2]|0,c[n>>2]&255);B=(c[g>>2]|0)+40|0;c[B>>2]=(c[B>>2]|0)+1;c[l>>2]=(c[l>>2]|0)+1}if((D|0)==40){c[s>>2]=1}td(c[t>>2]|0);c[f>>2]=c[s>>2];C=c[f>>2]|0;i=e;return C|0}function Rf(b,e,f,g){b=b|0;e=e|0;f=f|0;g=g|0;var h=0,j=0,k=0,l=0,m=0,n=0,o=0;h=i;i=i+32|0;j=h+16|0;k=h+12|0;l=h+8|0;m=h+20|0;n=h+4|0;o=h;c[j>>2]=b;c[k>>2]=e;c[l>>2]=f;a[m]=g;c[n>>2]=~(1<<(d[m]|0));c[o>>2]=c[c[j>>2]>>2];m=(c[(c[j>>2]|0)+16>>2]|0)+(c[l>>2]<<2)|0;c[m>>2]=c[m>>2]&c[n>>2];m=(c[(c[j>>2]|0)+20>>2]|0)+(c[k>>2]<<2)|0;c[m>>2]=c[m>>2]&c[n>>2];m=Z(c[l>>2]|0,c[o>>2]|0)|0;g=(c[(c[j>>2]|0)+24>>2]|0)+(c[(c[(c[(c[j>>2]|0)+4>>2]|0)+16>>2]|0)+(m+(c[k>>2]|0)<<2)>>2]<<2)|0;c[g>>2]=c[g>>2]&c[n>>2];if((c[(c[j>>2]|0)+28>>2]|0)!=0){g=Z(c[l>>2]|0,c[o>>2]|0)|0;m=(c[(c[j>>2]|0)+28>>2]|0)+(c[(c[(c[(c[j>>2]|0)+8>>2]|0)+16>>2]|0)+(g+(c[k>>2]|0)<<2)>>2]<<2)|0;c[m>>2]=c[m>>2]&c[n>>2]}if((c[(c[j>>2]|0)+32>>2]|0)!=0){m=Z(c[l>>2]|0,c[o>>2]|0)|0;if(((m+(c[k>>2]|0)|0)%((c[o>>2]|0)+1|0)|0|0)==0){m=c[(c[j>>2]|0)+32>>2]|0;c[m>>2]=c[m>>2]&c[n>>2]}m=Z(c[l>>2]|0,c[o>>2]|0)|0;if((((m+(c[k>>2]|0)|0)%((c[o>>2]|0)-1|0)|0|0)==0?(m=Z(c[l>>2]|0,c[o>>2]|0)|0,(m+(c[k>>2]|0)|0)>0):0)?(m=Z(c[l>>2]|0,c[o>>2]|0)|0,(m+(c[k>>2]|0)|0)<((Z(c[o>>2]|0,c[o>>2]|0)|0)-1|0)):0){m=(c[(c[j>>2]|0)+32>>2]|0)+4|0;c[m>>2]=c[m>>2]&c[n>>2]}}n=Z(c[l>>2]|0,c[o>>2]|0)|0;a[(c[(c[j>>2]|0)+12>>2]|0)+(n+(c[k>>2]|0))|0]=0;i=h;return}function Sf(b,c){b=b|0;c=c|0;var d=0,e=0;d=i;e=Tf(b,c)|0;i=d;return((a[e]|0)==(c&255)<<24>>24?e:0)|0}function Tf(b,d){b=b|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0;e=i;f=d&255;if((f|0)==0){g=b+(bg(b|0)|0)|0;i=e;return g|0}a:do{if((b&3|0)!=0){h=d&255;j=b;while(1){k=a[j]|0;if(k<<24>>24==0){g=j;l=13;break}m=j+1|0;if(k<<24>>24==h<<24>>24){g=j;l=13;break}if((m&3|0)==0){n=m;break a}else{j=m}}if((l|0)==13){i=e;return g|0}}else{n=b}}while(0);b=Z(f,16843009)|0;f=c[n>>2]|0;b:do{if(((f&-2139062144^-2139062144)&f+ -16843009|0)==0){l=f;j=n;while(1){h=l^b;m=j+4|0;if(((h&-2139062144^-2139062144)&h+ -16843009|0)!=0){o=j;break b}h=c[m>>2]|0;if(((h&-2139062144^-2139062144)&h+ -16843009|0)==0){l=h;j=m}else{o=m;break}}}else{o=n}}while(0);n=d&255;d=o;while(1){o=a[d]|0;if(o<<24>>24==0|o<<24>>24==n<<24>>24){g=d;break}else{d=d+1|0}}i=e;return g|0}



function Uf(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0,L=0,M=0,N=0,O=0,P=0,Q=0,R=0,S=0,T=0,U=0,V=0,W=0,X=0,Y=0,Z=0,_=0,$=0,aa=0,ba=0,ca=0,da=0,ea=0,fa=0,ga=0,ha=0,ia=0,ja=0,ka=0,la=0,ma=0,na=0,oa=0,pa=0,qa=0,ra=0,sa=0,ta=0,ua=0,va=0,wa=0,xa=0,ya=0,za=0,Aa=0,Ba=0,Ca=0,Da=0,Ea=0,Fa=0,Ga=0,Ha=0,Ia=0,Ka=0,La=0;b=i;do{if(a>>>0<245){if(a>>>0<11){d=16}else{d=a+11&-8}e=d>>>3;f=c[2114]|0;g=f>>>e;if((g&3|0)!=0){h=(g&1^1)+e|0;j=h<<1;k=8496+(j<<2)|0;l=8496+(j+2<<2)|0;j=c[l>>2]|0;m=j+8|0;n=c[m>>2]|0;do{if((k|0)!=(n|0)){if(n>>>0<(c[8472>>2]|0)>>>0){nb()}o=n+12|0;if((c[o>>2]|0)==(j|0)){c[o>>2]=k;c[l>>2]=n;break}else{nb()}}else{c[2114]=f&~(1<<h)}}while(0);n=h<<3;c[j+4>>2]=n|3;l=j+(n|4)|0;c[l>>2]=c[l>>2]|1;p=m;i=b;return p|0}if(d>>>0>(c[8464>>2]|0)>>>0){if((g|0)!=0){l=2<<e;n=g<<e&(l|0-l);l=(n&0-n)+ -1|0;n=l>>>12&16;k=l>>>n;l=k>>>5&8;o=k>>>l;k=o>>>2&4;q=o>>>k;o=q>>>1&2;r=q>>>o;q=r>>>1&1;s=(l|n|k|o|q)+(r>>>q)|0;q=s<<1;r=8496+(q<<2)|0;o=8496+(q+2<<2)|0;q=c[o>>2]|0;k=q+8|0;n=c[k>>2]|0;do{if((r|0)!=(n|0)){if(n>>>0<(c[8472>>2]|0)>>>0){nb()}l=n+12|0;if((c[l>>2]|0)==(q|0)){c[l>>2]=r;c[o>>2]=n;break}else{nb()}}else{c[2114]=f&~(1<<s)}}while(0);f=s<<3;n=f-d|0;c[q+4>>2]=d|3;o=q+d|0;c[q+(d|4)>>2]=n|1;c[q+f>>2]=n;f=c[8464>>2]|0;if((f|0)!=0){r=c[8476>>2]|0;e=f>>>3;f=e<<1;g=8496+(f<<2)|0;m=c[2114]|0;j=1<<e;if((m&j|0)!=0){e=8496+(f+2<<2)|0;h=c[e>>2]|0;if(h>>>0<(c[8472>>2]|0)>>>0){nb()}else{t=e;u=h}}else{c[2114]=m|j;t=8496+(f+2<<2)|0;u=g}c[t>>2]=r;c[u+12>>2]=r;c[r+8>>2]=u;c[r+12>>2]=g}c[8464>>2]=n;c[8476>>2]=o;p=k;i=b;return p|0}o=c[8460>>2]|0;if((o|0)!=0){n=(o&0-o)+ -1|0;o=n>>>12&16;g=n>>>o;n=g>>>5&8;r=g>>>n;g=r>>>2&4;f=r>>>g;r=f>>>1&2;j=f>>>r;f=j>>>1&1;m=c[8760+((n|o|g|r|f)+(j>>>f)<<2)>>2]|0;f=(c[m+4>>2]&-8)-d|0;j=m;r=m;while(1){m=c[j+16>>2]|0;if((m|0)==0){g=c[j+20>>2]|0;if((g|0)==0){break}else{v=g}}else{v=m}m=(c[v+4>>2]&-8)-d|0;g=m>>>0<f>>>0;f=g?m:f;j=v;r=g?v:r}j=c[8472>>2]|0;if(r>>>0<j>>>0){nb()}k=r+d|0;if(!(r>>>0<k>>>0)){nb()}q=c[r+24>>2]|0;s=c[r+12>>2]|0;do{if((s|0)==(r|0)){g=r+20|0;m=c[g>>2]|0;if((m|0)==0){o=r+16|0;n=c[o>>2]|0;if((n|0)==0){w=0;break}else{x=n;y=o}}else{x=m;y=g}while(1){g=x+20|0;m=c[g>>2]|0;if((m|0)!=0){x=m;y=g;continue}g=x+16|0;m=c[g>>2]|0;if((m|0)==0){break}else{x=m;y=g}}if(y>>>0<j>>>0){nb()}else{c[y>>2]=0;w=x;break}}else{g=c[r+8>>2]|0;if(g>>>0<j>>>0){nb()}m=g+12|0;if((c[m>>2]|0)!=(r|0)){nb()}o=s+8|0;if((c[o>>2]|0)==(r|0)){c[m>>2]=s;c[o>>2]=g;w=s;break}else{nb()}}}while(0);do{if((q|0)!=0){s=c[r+28>>2]|0;j=8760+(s<<2)|0;if((r|0)==(c[j>>2]|0)){c[j>>2]=w;if((w|0)==0){c[8460>>2]=c[8460>>2]&~(1<<s);break}}else{if(q>>>0<(c[8472>>2]|0)>>>0){nb()}s=q+16|0;if((c[s>>2]|0)==(r|0)){c[s>>2]=w}else{c[q+20>>2]=w}if((w|0)==0){break}}if(w>>>0<(c[8472>>2]|0)>>>0){nb()}c[w+24>>2]=q;s=c[r+16>>2]|0;do{if((s|0)!=0){if(s>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[w+16>>2]=s;c[s+24>>2]=w;break}}}while(0);s=c[r+20>>2]|0;if((s|0)!=0){if(s>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[w+20>>2]=s;c[s+24>>2]=w;break}}}}while(0);if(f>>>0<16){q=f+d|0;c[r+4>>2]=q|3;s=r+(q+4)|0;c[s>>2]=c[s>>2]|1}else{c[r+4>>2]=d|3;c[r+(d|4)>>2]=f|1;c[r+(f+d)>>2]=f;s=c[8464>>2]|0;if((s|0)!=0){q=c[8476>>2]|0;j=s>>>3;s=j<<1;g=8496+(s<<2)|0;o=c[2114]|0;m=1<<j;if((o&m|0)!=0){j=8496+(s+2<<2)|0;n=c[j>>2]|0;if(n>>>0<(c[8472>>2]|0)>>>0){nb()}else{z=j;A=n}}else{c[2114]=o|m;z=8496+(s+2<<2)|0;A=g}c[z>>2]=q;c[A+12>>2]=q;c[q+8>>2]=A;c[q+12>>2]=g}c[8464>>2]=f;c[8476>>2]=k}p=r+8|0;i=b;return p|0}else{B=d}}else{B=d}}else{if(!(a>>>0>4294967231)){g=a+11|0;q=g&-8;s=c[8460>>2]|0;if((s|0)!=0){m=0-q|0;o=g>>>8;if((o|0)!=0){if(q>>>0>16777215){C=31}else{g=(o+1048320|0)>>>16&8;n=o<<g;o=(n+520192|0)>>>16&4;j=n<<o;n=(j+245760|0)>>>16&2;h=14-(o|g|n)+(j<<n>>>15)|0;C=q>>>(h+7|0)&1|h<<1}}else{C=0}h=c[8760+(C<<2)>>2]|0;a:do{if((h|0)==0){D=m;E=0;F=0}else{if((C|0)==31){G=0}else{G=25-(C>>>1)|0}n=m;j=0;g=q<<G;o=h;e=0;while(1){l=c[o+4>>2]&-8;H=l-q|0;if(H>>>0<n>>>0){if((l|0)==(q|0)){D=H;E=o;F=o;break a}else{I=H;J=o}}else{I=n;J=e}H=c[o+20>>2]|0;l=c[o+(g>>>31<<2)+16>>2]|0;K=(H|0)==0|(H|0)==(l|0)?j:H;if((l|0)==0){D=I;E=K;F=J;break}else{n=I;j=K;g=g<<1;o=l;e=J}}}}while(0);if((E|0)==0&(F|0)==0){h=2<<C;m=s&(h|0-h);if((m|0)==0){B=q;break}h=(m&0-m)+ -1|0;m=h>>>12&16;r=h>>>m;h=r>>>5&8;k=r>>>h;r=k>>>2&4;f=k>>>r;k=f>>>1&2;e=f>>>k;f=e>>>1&1;L=c[8760+((h|m|r|k|f)+(e>>>f)<<2)>>2]|0}else{L=E}if((L|0)==0){M=D;N=F}else{f=D;e=L;k=F;while(1){r=(c[e+4>>2]&-8)-q|0;m=r>>>0<f>>>0;h=m?r:f;r=m?e:k;m=c[e+16>>2]|0;if((m|0)!=0){f=h;e=m;k=r;continue}m=c[e+20>>2]|0;if((m|0)==0){M=h;N=r;break}else{f=h;e=m;k=r}}}if((N|0)!=0?M>>>0<((c[8464>>2]|0)-q|0)>>>0:0){k=c[8472>>2]|0;if(N>>>0<k>>>0){nb()}e=N+q|0;if(!(N>>>0<e>>>0)){nb()}f=c[N+24>>2]|0;s=c[N+12>>2]|0;do{if((s|0)==(N|0)){r=N+20|0;m=c[r>>2]|0;if((m|0)==0){h=N+16|0;o=c[h>>2]|0;if((o|0)==0){O=0;break}else{P=o;Q=h}}else{P=m;Q=r}while(1){r=P+20|0;m=c[r>>2]|0;if((m|0)!=0){P=m;Q=r;continue}r=P+16|0;m=c[r>>2]|0;if((m|0)==0){break}else{P=m;Q=r}}if(Q>>>0<k>>>0){nb()}else{c[Q>>2]=0;O=P;break}}else{r=c[N+8>>2]|0;if(r>>>0<k>>>0){nb()}m=r+12|0;if((c[m>>2]|0)!=(N|0)){nb()}h=s+8|0;if((c[h>>2]|0)==(N|0)){c[m>>2]=s;c[h>>2]=r;O=s;break}else{nb()}}}while(0);do{if((f|0)!=0){s=c[N+28>>2]|0;k=8760+(s<<2)|0;if((N|0)==(c[k>>2]|0)){c[k>>2]=O;if((O|0)==0){c[8460>>2]=c[8460>>2]&~(1<<s);break}}else{if(f>>>0<(c[8472>>2]|0)>>>0){nb()}s=f+16|0;if((c[s>>2]|0)==(N|0)){c[s>>2]=O}else{c[f+20>>2]=O}if((O|0)==0){break}}if(O>>>0<(c[8472>>2]|0)>>>0){nb()}c[O+24>>2]=f;s=c[N+16>>2]|0;do{if((s|0)!=0){if(s>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[O+16>>2]=s;c[s+24>>2]=O;break}}}while(0);s=c[N+20>>2]|0;if((s|0)!=0){if(s>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[O+20>>2]=s;c[s+24>>2]=O;break}}}}while(0);b:do{if(!(M>>>0<16)){c[N+4>>2]=q|3;c[N+(q|4)>>2]=M|1;c[N+(M+q)>>2]=M;f=M>>>3;if(M>>>0<256){s=f<<1;k=8496+(s<<2)|0;r=c[2114]|0;h=1<<f;if((r&h|0)!=0){f=8496+(s+2<<2)|0;m=c[f>>2]|0;if(m>>>0<(c[8472>>2]|0)>>>0){nb()}else{R=f;S=m}}else{c[2114]=r|h;R=8496+(s+2<<2)|0;S=k}c[R>>2]=e;c[S+12>>2]=e;c[N+(q+8)>>2]=S;c[N+(q+12)>>2]=k;break}k=M>>>8;if((k|0)!=0){if(M>>>0>16777215){T=31}else{s=(k+1048320|0)>>>16&8;h=k<<s;k=(h+520192|0)>>>16&4;r=h<<k;h=(r+245760|0)>>>16&2;m=14-(k|s|h)+(r<<h>>>15)|0;T=M>>>(m+7|0)&1|m<<1}}else{T=0}m=8760+(T<<2)|0;c[N+(q+28)>>2]=T;c[N+(q+20)>>2]=0;c[N+(q+16)>>2]=0;h=c[8460>>2]|0;r=1<<T;if((h&r|0)==0){c[8460>>2]=h|r;c[m>>2]=e;c[N+(q+24)>>2]=m;c[N+(q+12)>>2]=e;c[N+(q+8)>>2]=e;break}r=c[m>>2]|0;if((T|0)==31){U=0}else{U=25-(T>>>1)|0}c:do{if((c[r+4>>2]&-8|0)!=(M|0)){m=M<<U;h=r;while(1){V=h+(m>>>31<<2)+16|0;s=c[V>>2]|0;if((s|0)==0){break}if((c[s+4>>2]&-8|0)==(M|0)){W=s;break c}else{m=m<<1;h=s}}if(V>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[V>>2]=e;c[N+(q+24)>>2]=h;c[N+(q+12)>>2]=e;c[N+(q+8)>>2]=e;break b}}else{W=r}}while(0);r=W+8|0;m=c[r>>2]|0;s=c[8472>>2]|0;if(W>>>0<s>>>0){nb()}if(m>>>0<s>>>0){nb()}else{c[m+12>>2]=e;c[r>>2]=e;c[N+(q+8)>>2]=m;c[N+(q+12)>>2]=W;c[N+(q+24)>>2]=0;break}}else{m=M+q|0;c[N+4>>2]=m|3;r=N+(m+4)|0;c[r>>2]=c[r>>2]|1}}while(0);p=N+8|0;i=b;return p|0}else{B=q}}else{B=q}}else{B=-1}}}while(0);N=c[8464>>2]|0;if(!(B>>>0>N>>>0)){M=N-B|0;W=c[8476>>2]|0;if(M>>>0>15){c[8476>>2]=W+B;c[8464>>2]=M;c[W+(B+4)>>2]=M|1;c[W+N>>2]=M;c[W+4>>2]=B|3}else{c[8464>>2]=0;c[8476>>2]=0;c[W+4>>2]=N|3;M=W+(N+4)|0;c[M>>2]=c[M>>2]|1}p=W+8|0;i=b;return p|0}W=c[8468>>2]|0;if(B>>>0<W>>>0){M=W-B|0;c[8468>>2]=M;W=c[8480>>2]|0;c[8480>>2]=W+B;c[W+(B+4)>>2]=M|1;c[W+4>>2]=B|3;p=W+8|0;i=b;return p|0}do{if((c[2232]|0)==0){W=Ra(30)|0;if((W+ -1&W|0)==0){c[8936>>2]=W;c[8932>>2]=W;c[8940>>2]=-1;c[8944>>2]=-1;c[8948>>2]=0;c[8900>>2]=0;c[2232]=(qb(0)|0)&-16^1431655768;break}else{nb()}}}while(0);W=B+48|0;M=c[8936>>2]|0;N=B+47|0;V=M+N|0;U=0-M|0;M=V&U;if(!(M>>>0>B>>>0)){p=0;i=b;return p|0}T=c[8896>>2]|0;if((T|0)!=0?(S=c[8888>>2]|0,R=S+M|0,R>>>0<=S>>>0|R>>>0>T>>>0):0){p=0;i=b;return p|0}d:do{if((c[8900>>2]&4|0)==0){T=c[8480>>2]|0;e:do{if((T|0)!=0){R=8904|0;while(1){S=c[R>>2]|0;if(!(S>>>0>T>>>0)?(X=R+4|0,(S+(c[X>>2]|0)|0)>>>0>T>>>0):0){break}S=c[R+8>>2]|0;if((S|0)==0){Y=182;break e}else{R=S}}if((R|0)!=0){S=V-(c[8468>>2]|0)&U;if(S>>>0<2147483647){O=Ja(S|0)|0;P=(O|0)==((c[R>>2]|0)+(c[X>>2]|0)|0);Z=O;_=S;$=P?O:-1;aa=P?S:0;Y=191}else{ba=0}}else{Y=182}}else{Y=182}}while(0);do{if((Y|0)==182){T=Ja(0)|0;if((T|0)!=(-1|0)){q=T;S=c[8932>>2]|0;P=S+ -1|0;if((P&q|0)==0){ca=M}else{ca=M-q+(P+q&0-S)|0}S=c[8888>>2]|0;q=S+ca|0;if(ca>>>0>B>>>0&ca>>>0<2147483647){P=c[8896>>2]|0;if((P|0)!=0?q>>>0<=S>>>0|q>>>0>P>>>0:0){ba=0;break}P=Ja(ca|0)|0;q=(P|0)==(T|0);Z=P;_=ca;$=q?T:-1;aa=q?ca:0;Y=191}else{ba=0}}else{ba=0}}}while(0);f:do{if((Y|0)==191){q=0-_|0;if(($|0)!=(-1|0)){da=$;ea=aa;Y=202;break d}do{if((Z|0)!=(-1|0)&_>>>0<2147483647&_>>>0<W>>>0?(T=c[8936>>2]|0,P=N-_+T&0-T,P>>>0<2147483647):0){if((Ja(P|0)|0)==(-1|0)){Ja(q|0)|0;ba=aa;break f}else{fa=P+_|0;break}}else{fa=_}}while(0);if((Z|0)==(-1|0)){ba=aa}else{da=Z;ea=fa;Y=202;break d}}}while(0);c[8900>>2]=c[8900>>2]|4;ga=ba;Y=199}else{ga=0;Y=199}}while(0);if((((Y|0)==199?M>>>0<2147483647:0)?(ba=Ja(M|0)|0,M=Ja(0)|0,(M|0)!=(-1|0)&(ba|0)!=(-1|0)&ba>>>0<M>>>0):0)?(fa=M-ba|0,M=fa>>>0>(B+40|0)>>>0,M):0){da=ba;ea=M?fa:ga;Y=202}if((Y|0)==202){ga=(c[8888>>2]|0)+ea|0;c[8888>>2]=ga;if(ga>>>0>(c[8892>>2]|0)>>>0){c[8892>>2]=ga}ga=c[8480>>2]|0;g:do{if((ga|0)!=0){fa=8904|0;while(1){ha=c[fa>>2]|0;ia=fa+4|0;ja=c[ia>>2]|0;if((da|0)==(ha+ja|0)){Y=214;break}M=c[fa+8>>2]|0;if((M|0)==0){break}else{fa=M}}if(((Y|0)==214?(c[fa+12>>2]&8|0)==0:0)?ga>>>0>=ha>>>0&ga>>>0<da>>>0:0){c[ia>>2]=ja+ea;M=(c[8468>>2]|0)+ea|0;ba=ga+8|0;if((ba&7|0)==0){ka=0}else{ka=0-ba&7}ba=M-ka|0;c[8480>>2]=ga+ka;c[8468>>2]=ba;c[ga+(ka+4)>>2]=ba|1;c[ga+(M+4)>>2]=40;c[8484>>2]=c[8944>>2];break}if(da>>>0<(c[8472>>2]|0)>>>0){c[8472>>2]=da}M=da+ea|0;ba=8904|0;while(1){if((c[ba>>2]|0)==(M|0)){Y=224;break}Z=c[ba+8>>2]|0;if((Z|0)==0){break}else{ba=Z}}if((Y|0)==224?(c[ba+12>>2]&8|0)==0:0){c[ba>>2]=da;M=ba+4|0;c[M>>2]=(c[M>>2]|0)+ea;M=da+8|0;if((M&7|0)==0){la=0}else{la=0-M&7}M=da+(ea+8)|0;if((M&7|0)==0){ma=0}else{ma=0-M&7}M=da+(ma+ea)|0;fa=la+B|0;Z=da+fa|0;aa=M-(da+la)-B|0;c[da+(la+4)>>2]=B|3;h:do{if((M|0)!=(c[8480>>2]|0)){if((M|0)==(c[8476>>2]|0)){_=(c[8464>>2]|0)+aa|0;c[8464>>2]=_;c[8476>>2]=Z;c[da+(fa+4)>>2]=_|1;c[da+(_+fa)>>2]=_;break}_=ea+4|0;N=c[da+(_+ma)>>2]|0;if((N&3|0)==1){W=N&-8;$=N>>>3;do{if(!(N>>>0<256)){ca=c[da+((ma|24)+ea)>>2]|0;X=c[da+(ea+12+ma)>>2]|0;do{if((X|0)==(M|0)){U=ma|16;V=da+(_+U)|0;q=c[V>>2]|0;if((q|0)==0){R=da+(U+ea)|0;U=c[R>>2]|0;if((U|0)==0){na=0;break}else{oa=U;pa=R}}else{oa=q;pa=V}while(1){V=oa+20|0;q=c[V>>2]|0;if((q|0)!=0){oa=q;pa=V;continue}V=oa+16|0;q=c[V>>2]|0;if((q|0)==0){break}else{oa=q;pa=V}}if(pa>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[pa>>2]=0;na=oa;break}}else{V=c[da+((ma|8)+ea)>>2]|0;if(V>>>0<(c[8472>>2]|0)>>>0){nb()}q=V+12|0;if((c[q>>2]|0)!=(M|0)){nb()}R=X+8|0;if((c[R>>2]|0)==(M|0)){c[q>>2]=X;c[R>>2]=V;na=X;break}else{nb()}}}while(0);if((ca|0)!=0){X=c[da+(ea+28+ma)>>2]|0;h=8760+(X<<2)|0;if((M|0)==(c[h>>2]|0)){c[h>>2]=na;if((na|0)==0){c[8460>>2]=c[8460>>2]&~(1<<X);break}}else{if(ca>>>0<(c[8472>>2]|0)>>>0){nb()}X=ca+16|0;if((c[X>>2]|0)==(M|0)){c[X>>2]=na}else{c[ca+20>>2]=na}if((na|0)==0){break}}if(na>>>0<(c[8472>>2]|0)>>>0){nb()}c[na+24>>2]=ca;X=ma|16;h=c[da+(X+ea)>>2]|0;do{if((h|0)!=0){if(h>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[na+16>>2]=h;c[h+24>>2]=na;break}}}while(0);h=c[da+(_+X)>>2]|0;if((h|0)!=0){if(h>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[na+20>>2]=h;c[h+24>>2]=na;break}}}}else{h=c[da+((ma|8)+ea)>>2]|0;ca=c[da+(ea+12+ma)>>2]|0;V=8496+($<<1<<2)|0;if((h|0)!=(V|0)){if(h>>>0<(c[8472>>2]|0)>>>0){nb()}if((c[h+12>>2]|0)!=(M|0)){nb()}}if((ca|0)==(h|0)){c[2114]=c[2114]&~(1<<$);break}if((ca|0)!=(V|0)){if(ca>>>0<(c[8472>>2]|0)>>>0){nb()}V=ca+8|0;if((c[V>>2]|0)==(M|0)){qa=V}else{nb()}}else{qa=ca+8|0}c[h+12>>2]=ca;c[qa>>2]=h}}while(0);ra=da+((W|ma)+ea)|0;sa=W+aa|0}else{ra=M;sa=aa}$=ra+4|0;c[$>>2]=c[$>>2]&-2;c[da+(fa+4)>>2]=sa|1;c[da+(sa+fa)>>2]=sa;$=sa>>>3;if(sa>>>0<256){_=$<<1;N=8496+(_<<2)|0;h=c[2114]|0;ca=1<<$;if((h&ca|0)!=0){$=8496+(_+2<<2)|0;V=c[$>>2]|0;if(V>>>0<(c[8472>>2]|0)>>>0){nb()}else{ta=$;ua=V}}else{c[2114]=h|ca;ta=8496+(_+2<<2)|0;ua=N}c[ta>>2]=Z;c[ua+12>>2]=Z;c[da+(fa+8)>>2]=ua;c[da+(fa+12)>>2]=N;break}N=sa>>>8;if((N|0)!=0){if(sa>>>0>16777215){va=31}else{_=(N+1048320|0)>>>16&8;ca=N<<_;N=(ca+520192|0)>>>16&4;h=ca<<N;ca=(h+245760|0)>>>16&2;V=14-(N|_|ca)+(h<<ca>>>15)|0;va=sa>>>(V+7|0)&1|V<<1}}else{va=0}V=8760+(va<<2)|0;c[da+(fa+28)>>2]=va;c[da+(fa+20)>>2]=0;c[da+(fa+16)>>2]=0;ca=c[8460>>2]|0;h=1<<va;if((ca&h|0)==0){c[8460>>2]=ca|h;c[V>>2]=Z;c[da+(fa+24)>>2]=V;c[da+(fa+12)>>2]=Z;c[da+(fa+8)>>2]=Z;break}h=c[V>>2]|0;if((va|0)==31){wa=0}else{wa=25-(va>>>1)|0}i:do{if((c[h+4>>2]&-8|0)!=(sa|0)){V=sa<<wa;ca=h;while(1){xa=ca+(V>>>31<<2)+16|0;_=c[xa>>2]|0;if((_|0)==0){break}if((c[_+4>>2]&-8|0)==(sa|0)){ya=_;break i}else{V=V<<1;ca=_}}if(xa>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[xa>>2]=Z;c[da+(fa+24)>>2]=ca;c[da+(fa+12)>>2]=Z;c[da+(fa+8)>>2]=Z;break h}}else{ya=h}}while(0);h=ya+8|0;W=c[h>>2]|0;V=c[8472>>2]|0;if(ya>>>0<V>>>0){nb()}if(W>>>0<V>>>0){nb()}else{c[W+12>>2]=Z;c[h>>2]=Z;c[da+(fa+8)>>2]=W;c[da+(fa+12)>>2]=ya;c[da+(fa+24)>>2]=0;break}}else{W=(c[8468>>2]|0)+aa|0;c[8468>>2]=W;c[8480>>2]=Z;c[da+(fa+4)>>2]=W|1}}while(0);p=da+(la|8)|0;i=b;return p|0}fa=8904|0;while(1){za=c[fa>>2]|0;if(!(za>>>0>ga>>>0)?(Aa=c[fa+4>>2]|0,Ba=za+Aa|0,Ba>>>0>ga>>>0):0){break}fa=c[fa+8>>2]|0}fa=za+(Aa+ -39)|0;if((fa&7|0)==0){Ca=0}else{Ca=0-fa&7}fa=za+(Aa+ -47+Ca)|0;Z=fa>>>0<(ga+16|0)>>>0?ga:fa;fa=Z+8|0;aa=da+8|0;if((aa&7|0)==0){Da=0}else{Da=0-aa&7}aa=ea+ -40-Da|0;c[8480>>2]=da+Da;c[8468>>2]=aa;c[da+(Da+4)>>2]=aa|1;c[da+(ea+ -36)>>2]=40;c[8484>>2]=c[8944>>2];c[Z+4>>2]=27;c[fa+0>>2]=c[8904>>2];c[fa+4>>2]=c[8908>>2];c[fa+8>>2]=c[8912>>2];c[fa+12>>2]=c[8916>>2];c[8904>>2]=da;c[8908>>2]=ea;c[8916>>2]=0;c[8912>>2]=fa;fa=Z+28|0;c[fa>>2]=7;if((Z+32|0)>>>0<Ba>>>0){aa=fa;do{fa=aa;aa=aa+4|0;c[aa>>2]=7}while((fa+8|0)>>>0<Ba>>>0)}if((Z|0)!=(ga|0)){aa=Z-ga|0;fa=ga+(aa+4)|0;c[fa>>2]=c[fa>>2]&-2;c[ga+4>>2]=aa|1;c[ga+aa>>2]=aa;fa=aa>>>3;if(aa>>>0<256){M=fa<<1;ba=8496+(M<<2)|0;W=c[2114]|0;h=1<<fa;if((W&h|0)!=0){fa=8496+(M+2<<2)|0;V=c[fa>>2]|0;if(V>>>0<(c[8472>>2]|0)>>>0){nb()}else{Ea=fa;Fa=V}}else{c[2114]=W|h;Ea=8496+(M+2<<2)|0;Fa=ba}c[Ea>>2]=ga;c[Fa+12>>2]=ga;c[ga+8>>2]=Fa;c[ga+12>>2]=ba;break}ba=aa>>>8;if((ba|0)!=0){if(aa>>>0>16777215){Ga=31}else{M=(ba+1048320|0)>>>16&8;h=ba<<M;ba=(h+520192|0)>>>16&4;W=h<<ba;h=(W+245760|0)>>>16&2;V=14-(ba|M|h)+(W<<h>>>15)|0;Ga=aa>>>(V+7|0)&1|V<<1}}else{Ga=0}V=8760+(Ga<<2)|0;c[ga+28>>2]=Ga;c[ga+20>>2]=0;c[ga+16>>2]=0;h=c[8460>>2]|0;W=1<<Ga;if((h&W|0)==0){c[8460>>2]=h|W;c[V>>2]=ga;c[ga+24>>2]=V;c[ga+12>>2]=ga;c[ga+8>>2]=ga;break}W=c[V>>2]|0;if((Ga|0)==31){Ha=0}else{Ha=25-(Ga>>>1)|0}j:do{if((c[W+4>>2]&-8|0)!=(aa|0)){V=aa<<Ha;h=W;while(1){Ia=h+(V>>>31<<2)+16|0;M=c[Ia>>2]|0;if((M|0)==0){break}if((c[M+4>>2]&-8|0)==(aa|0)){Ka=M;break j}else{V=V<<1;h=M}}if(Ia>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[Ia>>2]=ga;c[ga+24>>2]=h;c[ga+12>>2]=ga;c[ga+8>>2]=ga;break g}}else{Ka=W}}while(0);W=Ka+8|0;aa=c[W>>2]|0;Z=c[8472>>2]|0;if(Ka>>>0<Z>>>0){nb()}if(aa>>>0<Z>>>0){nb()}else{c[aa+12>>2]=ga;c[W>>2]=ga;c[ga+8>>2]=aa;c[ga+12>>2]=Ka;c[ga+24>>2]=0;break}}}else{aa=c[8472>>2]|0;if((aa|0)==0|da>>>0<aa>>>0){c[8472>>2]=da}c[8904>>2]=da;c[8908>>2]=ea;c[8916>>2]=0;c[8492>>2]=c[2232];c[8488>>2]=-1;aa=0;do{W=aa<<1;Z=8496+(W<<2)|0;c[8496+(W+3<<2)>>2]=Z;c[8496+(W+2<<2)>>2]=Z;aa=aa+1|0}while((aa|0)!=32);aa=da+8|0;if((aa&7|0)==0){La=0}else{La=0-aa&7}aa=ea+ -40-La|0;c[8480>>2]=da+La;c[8468>>2]=aa;c[da+(La+4)>>2]=aa|1;c[da+(ea+ -36)>>2]=40;c[8484>>2]=c[8944>>2]}}while(0);ea=c[8468>>2]|0;if(ea>>>0>B>>>0){da=ea-B|0;c[8468>>2]=da;ea=c[8480>>2]|0;c[8480>>2]=ea+B;c[ea+(B+4)>>2]=da|1;c[ea+4>>2]=B|3;p=ea+8|0;i=b;return p|0}}c[(Na()|0)>>2]=12;p=0;i=b;return p|0}function Vf(a){a=a|0;var b=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0,I=0,J=0,K=0;b=i;if((a|0)==0){i=b;return}d=a+ -8|0;e=c[8472>>2]|0;if(d>>>0<e>>>0){nb()}f=c[a+ -4>>2]|0;g=f&3;if((g|0)==1){nb()}h=f&-8;j=a+(h+ -8)|0;do{if((f&1|0)==0){k=c[d>>2]|0;if((g|0)==0){i=b;return}l=-8-k|0;m=a+l|0;n=k+h|0;if(m>>>0<e>>>0){nb()}if((m|0)==(c[8476>>2]|0)){o=a+(h+ -4)|0;if((c[o>>2]&3|0)!=3){p=m;q=n;break}c[8464>>2]=n;c[o>>2]=c[o>>2]&-2;c[a+(l+4)>>2]=n|1;c[j>>2]=n;i=b;return}o=k>>>3;if(k>>>0<256){k=c[a+(l+8)>>2]|0;r=c[a+(l+12)>>2]|0;s=8496+(o<<1<<2)|0;if((k|0)!=(s|0)){if(k>>>0<e>>>0){nb()}if((c[k+12>>2]|0)!=(m|0)){nb()}}if((r|0)==(k|0)){c[2114]=c[2114]&~(1<<o);p=m;q=n;break}if((r|0)!=(s|0)){if(r>>>0<e>>>0){nb()}s=r+8|0;if((c[s>>2]|0)==(m|0)){t=s}else{nb()}}else{t=r+8|0}c[k+12>>2]=r;c[t>>2]=k;p=m;q=n;break}k=c[a+(l+24)>>2]|0;r=c[a+(l+12)>>2]|0;do{if((r|0)==(m|0)){s=a+(l+20)|0;o=c[s>>2]|0;if((o|0)==0){u=a+(l+16)|0;v=c[u>>2]|0;if((v|0)==0){w=0;break}else{x=v;y=u}}else{x=o;y=s}while(1){s=x+20|0;o=c[s>>2]|0;if((o|0)!=0){x=o;y=s;continue}s=x+16|0;o=c[s>>2]|0;if((o|0)==0){break}else{x=o;y=s}}if(y>>>0<e>>>0){nb()}else{c[y>>2]=0;w=x;break}}else{s=c[a+(l+8)>>2]|0;if(s>>>0<e>>>0){nb()}o=s+12|0;if((c[o>>2]|0)!=(m|0)){nb()}u=r+8|0;if((c[u>>2]|0)==(m|0)){c[o>>2]=r;c[u>>2]=s;w=r;break}else{nb()}}}while(0);if((k|0)!=0){r=c[a+(l+28)>>2]|0;s=8760+(r<<2)|0;if((m|0)==(c[s>>2]|0)){c[s>>2]=w;if((w|0)==0){c[8460>>2]=c[8460>>2]&~(1<<r);p=m;q=n;break}}else{if(k>>>0<(c[8472>>2]|0)>>>0){nb()}r=k+16|0;if((c[r>>2]|0)==(m|0)){c[r>>2]=w}else{c[k+20>>2]=w}if((w|0)==0){p=m;q=n;break}}if(w>>>0<(c[8472>>2]|0)>>>0){nb()}c[w+24>>2]=k;r=c[a+(l+16)>>2]|0;do{if((r|0)!=0){if(r>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[w+16>>2]=r;c[r+24>>2]=w;break}}}while(0);r=c[a+(l+20)>>2]|0;if((r|0)!=0){if(r>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[w+20>>2]=r;c[r+24>>2]=w;p=m;q=n;break}}else{p=m;q=n}}else{p=m;q=n}}else{p=d;q=h}}while(0);if(!(p>>>0<j>>>0)){nb()}d=a+(h+ -4)|0;w=c[d>>2]|0;if((w&1|0)==0){nb()}if((w&2|0)==0){if((j|0)==(c[8480>>2]|0)){e=(c[8468>>2]|0)+q|0;c[8468>>2]=e;c[8480>>2]=p;c[p+4>>2]=e|1;if((p|0)!=(c[8476>>2]|0)){i=b;return}c[8476>>2]=0;c[8464>>2]=0;i=b;return}if((j|0)==(c[8476>>2]|0)){e=(c[8464>>2]|0)+q|0;c[8464>>2]=e;c[8476>>2]=p;c[p+4>>2]=e|1;c[p+e>>2]=e;i=b;return}e=(w&-8)+q|0;x=w>>>3;do{if(!(w>>>0<256)){y=c[a+(h+16)>>2]|0;t=c[a+(h|4)>>2]|0;do{if((t|0)==(j|0)){g=a+(h+12)|0;f=c[g>>2]|0;if((f|0)==0){r=a+(h+8)|0;k=c[r>>2]|0;if((k|0)==0){z=0;break}else{A=k;B=r}}else{A=f;B=g}while(1){g=A+20|0;f=c[g>>2]|0;if((f|0)!=0){A=f;B=g;continue}g=A+16|0;f=c[g>>2]|0;if((f|0)==0){break}else{A=f;B=g}}if(B>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[B>>2]=0;z=A;break}}else{g=c[a+h>>2]|0;if(g>>>0<(c[8472>>2]|0)>>>0){nb()}f=g+12|0;if((c[f>>2]|0)!=(j|0)){nb()}r=t+8|0;if((c[r>>2]|0)==(j|0)){c[f>>2]=t;c[r>>2]=g;z=t;break}else{nb()}}}while(0);if((y|0)!=0){t=c[a+(h+20)>>2]|0;n=8760+(t<<2)|0;if((j|0)==(c[n>>2]|0)){c[n>>2]=z;if((z|0)==0){c[8460>>2]=c[8460>>2]&~(1<<t);break}}else{if(y>>>0<(c[8472>>2]|0)>>>0){nb()}t=y+16|0;if((c[t>>2]|0)==(j|0)){c[t>>2]=z}else{c[y+20>>2]=z}if((z|0)==0){break}}if(z>>>0<(c[8472>>2]|0)>>>0){nb()}c[z+24>>2]=y;t=c[a+(h+8)>>2]|0;do{if((t|0)!=0){if(t>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[z+16>>2]=t;c[t+24>>2]=z;break}}}while(0);t=c[a+(h+12)>>2]|0;if((t|0)!=0){if(t>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[z+20>>2]=t;c[t+24>>2]=z;break}}}}else{t=c[a+h>>2]|0;y=c[a+(h|4)>>2]|0;n=8496+(x<<1<<2)|0;if((t|0)!=(n|0)){if(t>>>0<(c[8472>>2]|0)>>>0){nb()}if((c[t+12>>2]|0)!=(j|0)){nb()}}if((y|0)==(t|0)){c[2114]=c[2114]&~(1<<x);break}if((y|0)!=(n|0)){if(y>>>0<(c[8472>>2]|0)>>>0){nb()}n=y+8|0;if((c[n>>2]|0)==(j|0)){C=n}else{nb()}}else{C=y+8|0}c[t+12>>2]=y;c[C>>2]=t}}while(0);c[p+4>>2]=e|1;c[p+e>>2]=e;if((p|0)==(c[8476>>2]|0)){c[8464>>2]=e;i=b;return}else{D=e}}else{c[d>>2]=w&-2;c[p+4>>2]=q|1;c[p+q>>2]=q;D=q}q=D>>>3;if(D>>>0<256){w=q<<1;d=8496+(w<<2)|0;e=c[2114]|0;C=1<<q;if((e&C|0)!=0){q=8496+(w+2<<2)|0;j=c[q>>2]|0;if(j>>>0<(c[8472>>2]|0)>>>0){nb()}else{E=q;F=j}}else{c[2114]=e|C;E=8496+(w+2<<2)|0;F=d}c[E>>2]=p;c[F+12>>2]=p;c[p+8>>2]=F;c[p+12>>2]=d;i=b;return}d=D>>>8;if((d|0)!=0){if(D>>>0>16777215){G=31}else{F=(d+1048320|0)>>>16&8;E=d<<F;d=(E+520192|0)>>>16&4;w=E<<d;E=(w+245760|0)>>>16&2;C=14-(d|F|E)+(w<<E>>>15)|0;G=D>>>(C+7|0)&1|C<<1}}else{G=0}C=8760+(G<<2)|0;c[p+28>>2]=G;c[p+20>>2]=0;c[p+16>>2]=0;E=c[8460>>2]|0;w=1<<G;a:do{if((E&w|0)!=0){F=c[C>>2]|0;if((G|0)==31){H=0}else{H=25-(G>>>1)|0}b:do{if((c[F+4>>2]&-8|0)!=(D|0)){d=D<<H;e=F;while(1){I=e+(d>>>31<<2)+16|0;j=c[I>>2]|0;if((j|0)==0){break}if((c[j+4>>2]&-8|0)==(D|0)){J=j;break b}else{d=d<<1;e=j}}if(I>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[I>>2]=p;c[p+24>>2]=e;c[p+12>>2]=p;c[p+8>>2]=p;break a}}else{J=F}}while(0);F=J+8|0;d=c[F>>2]|0;j=c[8472>>2]|0;if(J>>>0<j>>>0){nb()}if(d>>>0<j>>>0){nb()}else{c[d+12>>2]=p;c[F>>2]=p;c[p+8>>2]=d;c[p+12>>2]=J;c[p+24>>2]=0;break}}else{c[8460>>2]=E|w;c[C>>2]=p;c[p+24>>2]=C;c[p+12>>2]=p;c[p+8>>2]=p}}while(0);p=(c[8488>>2]|0)+ -1|0;c[8488>>2]=p;if((p|0)==0){K=8912|0}else{i=b;return}while(1){p=c[K>>2]|0;if((p|0)==0){break}else{K=p+8|0}}c[8488>>2]=-1;i=b;return}function Wf(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0;d=i;do{if((a|0)!=0){if(b>>>0>4294967231){c[(Na()|0)>>2]=12;e=0;break}if(b>>>0<11){f=16}else{f=b+11&-8}g=Xf(a+ -8|0,f)|0;if((g|0)!=0){e=g+8|0;break}g=Uf(b)|0;if((g|0)==0){e=0}else{h=c[a+ -4>>2]|0;j=(h&-8)-((h&3|0)==0?8:4)|0;eg(g|0,a|0,(j>>>0<b>>>0?j:b)|0)|0;Vf(a);e=g}}else{e=Uf(b)|0}}while(0);i=d;return e|0}function Xf(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0;d=i;e=a+4|0;f=c[e>>2]|0;g=f&-8;h=a+g|0;j=c[8472>>2]|0;if(a>>>0<j>>>0){nb()}k=f&3;if(!((k|0)!=1&a>>>0<h>>>0)){nb()}l=a+(g|4)|0;m=c[l>>2]|0;if((m&1|0)==0){nb()}if((k|0)==0){if(b>>>0<256){n=0;i=d;return n|0}if(!(g>>>0<(b+4|0)>>>0)?!((g-b|0)>>>0>c[8936>>2]<<1>>>0):0){n=a;i=d;return n|0}n=0;i=d;return n|0}if(!(g>>>0<b>>>0)){k=g-b|0;if(!(k>>>0>15)){n=a;i=d;return n|0}c[e>>2]=f&1|b|2;c[a+(b+4)>>2]=k|3;c[l>>2]=c[l>>2]|1;Yf(a+b|0,k);n=a;i=d;return n|0}if((h|0)==(c[8480>>2]|0)){k=(c[8468>>2]|0)+g|0;if(!(k>>>0>b>>>0)){n=0;i=d;return n|0}l=k-b|0;c[e>>2]=f&1|b|2;c[a+(b+4)>>2]=l|1;c[8480>>2]=a+b;c[8468>>2]=l;n=a;i=d;return n|0}if((h|0)==(c[8476>>2]|0)){l=(c[8464>>2]|0)+g|0;if(l>>>0<b>>>0){n=0;i=d;return n|0}k=l-b|0;if(k>>>0>15){c[e>>2]=f&1|b|2;c[a+(b+4)>>2]=k|1;c[a+l>>2]=k;o=a+(l+4)|0;c[o>>2]=c[o>>2]&-2;p=a+b|0;q=k}else{c[e>>2]=f&1|l|2;f=a+(l+4)|0;c[f>>2]=c[f>>2]|1;p=0;q=0}c[8464>>2]=q;c[8476>>2]=p;n=a;i=d;return n|0}if((m&2|0)!=0){n=0;i=d;return n|0}p=(m&-8)+g|0;if(p>>>0<b>>>0){n=0;i=d;return n|0}q=p-b|0;f=m>>>3;do{if(!(m>>>0<256)){l=c[a+(g+24)>>2]|0;k=c[a+(g+12)>>2]|0;do{if((k|0)==(h|0)){o=a+(g+20)|0;r=c[o>>2]|0;if((r|0)==0){s=a+(g+16)|0;t=c[s>>2]|0;if((t|0)==0){u=0;break}else{v=t;w=s}}else{v=r;w=o}while(1){o=v+20|0;r=c[o>>2]|0;if((r|0)!=0){v=r;w=o;continue}o=v+16|0;r=c[o>>2]|0;if((r|0)==0){break}else{v=r;w=o}}if(w>>>0<j>>>0){nb()}else{c[w>>2]=0;u=v;break}}else{o=c[a+(g+8)>>2]|0;if(o>>>0<j>>>0){nb()}r=o+12|0;if((c[r>>2]|0)!=(h|0)){nb()}s=k+8|0;if((c[s>>2]|0)==(h|0)){c[r>>2]=k;c[s>>2]=o;u=k;break}else{nb()}}}while(0);if((l|0)!=0){k=c[a+(g+28)>>2]|0;o=8760+(k<<2)|0;if((h|0)==(c[o>>2]|0)){c[o>>2]=u;if((u|0)==0){c[8460>>2]=c[8460>>2]&~(1<<k);break}}else{if(l>>>0<(c[8472>>2]|0)>>>0){nb()}k=l+16|0;if((c[k>>2]|0)==(h|0)){c[k>>2]=u}else{c[l+20>>2]=u}if((u|0)==0){break}}if(u>>>0<(c[8472>>2]|0)>>>0){nb()}c[u+24>>2]=l;k=c[a+(g+16)>>2]|0;do{if((k|0)!=0){if(k>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[u+16>>2]=k;c[k+24>>2]=u;break}}}while(0);k=c[a+(g+20)>>2]|0;if((k|0)!=0){if(k>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[u+20>>2]=k;c[k+24>>2]=u;break}}}}else{k=c[a+(g+8)>>2]|0;l=c[a+(g+12)>>2]|0;o=8496+(f<<1<<2)|0;if((k|0)!=(o|0)){if(k>>>0<j>>>0){nb()}if((c[k+12>>2]|0)!=(h|0)){nb()}}if((l|0)==(k|0)){c[2114]=c[2114]&~(1<<f);break}if((l|0)!=(o|0)){if(l>>>0<j>>>0){nb()}o=l+8|0;if((c[o>>2]|0)==(h|0)){x=o}else{nb()}}else{x=l+8|0}c[k+12>>2]=l;c[x>>2]=k}}while(0);if(q>>>0<16){c[e>>2]=p|c[e>>2]&1|2;x=a+(p|4)|0;c[x>>2]=c[x>>2]|1;n=a;i=d;return n|0}else{c[e>>2]=c[e>>2]&1|b|2;c[a+(b+4)>>2]=q|3;e=a+(p|4)|0;c[e>>2]=c[e>>2]|1;Yf(a+b|0,q);n=a;i=d;return n|0}return 0}function Yf(a,b){a=a|0;b=b|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0,s=0,t=0,u=0,v=0,w=0,x=0,y=0,z=0,A=0,B=0,C=0,D=0,E=0,F=0,G=0,H=0;d=i;e=a+b|0;f=c[a+4>>2]|0;do{if((f&1|0)==0){g=c[a>>2]|0;if((f&3|0)==0){i=d;return}h=a+(0-g)|0;j=g+b|0;k=c[8472>>2]|0;if(h>>>0<k>>>0){nb()}if((h|0)==(c[8476>>2]|0)){l=a+(b+4)|0;if((c[l>>2]&3|0)!=3){m=h;n=j;break}c[8464>>2]=j;c[l>>2]=c[l>>2]&-2;c[a+(4-g)>>2]=j|1;c[e>>2]=j;i=d;return}l=g>>>3;if(g>>>0<256){o=c[a+(8-g)>>2]|0;p=c[a+(12-g)>>2]|0;q=8496+(l<<1<<2)|0;if((o|0)!=(q|0)){if(o>>>0<k>>>0){nb()}if((c[o+12>>2]|0)!=(h|0)){nb()}}if((p|0)==(o|0)){c[2114]=c[2114]&~(1<<l);m=h;n=j;break}if((p|0)!=(q|0)){if(p>>>0<k>>>0){nb()}q=p+8|0;if((c[q>>2]|0)==(h|0)){r=q}else{nb()}}else{r=p+8|0}c[o+12>>2]=p;c[r>>2]=o;m=h;n=j;break}o=c[a+(24-g)>>2]|0;p=c[a+(12-g)>>2]|0;do{if((p|0)==(h|0)){q=16-g|0;l=a+(q+4)|0;s=c[l>>2]|0;if((s|0)==0){t=a+q|0;q=c[t>>2]|0;if((q|0)==0){u=0;break}else{v=q;w=t}}else{v=s;w=l}while(1){l=v+20|0;s=c[l>>2]|0;if((s|0)!=0){v=s;w=l;continue}l=v+16|0;s=c[l>>2]|0;if((s|0)==0){break}else{v=s;w=l}}if(w>>>0<k>>>0){nb()}else{c[w>>2]=0;u=v;break}}else{l=c[a+(8-g)>>2]|0;if(l>>>0<k>>>0){nb()}s=l+12|0;if((c[s>>2]|0)!=(h|0)){nb()}t=p+8|0;if((c[t>>2]|0)==(h|0)){c[s>>2]=p;c[t>>2]=l;u=p;break}else{nb()}}}while(0);if((o|0)!=0){p=c[a+(28-g)>>2]|0;k=8760+(p<<2)|0;if((h|0)==(c[k>>2]|0)){c[k>>2]=u;if((u|0)==0){c[8460>>2]=c[8460>>2]&~(1<<p);m=h;n=j;break}}else{if(o>>>0<(c[8472>>2]|0)>>>0){nb()}p=o+16|0;if((c[p>>2]|0)==(h|0)){c[p>>2]=u}else{c[o+20>>2]=u}if((u|0)==0){m=h;n=j;break}}if(u>>>0<(c[8472>>2]|0)>>>0){nb()}c[u+24>>2]=o;p=16-g|0;k=c[a+p>>2]|0;do{if((k|0)!=0){if(k>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[u+16>>2]=k;c[k+24>>2]=u;break}}}while(0);k=c[a+(p+4)>>2]|0;if((k|0)!=0){if(k>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[u+20>>2]=k;c[k+24>>2]=u;m=h;n=j;break}}else{m=h;n=j}}else{m=h;n=j}}else{m=a;n=b}}while(0);u=c[8472>>2]|0;if(e>>>0<u>>>0){nb()}v=a+(b+4)|0;w=c[v>>2]|0;if((w&2|0)==0){if((e|0)==(c[8480>>2]|0)){r=(c[8468>>2]|0)+n|0;c[8468>>2]=r;c[8480>>2]=m;c[m+4>>2]=r|1;if((m|0)!=(c[8476>>2]|0)){i=d;return}c[8476>>2]=0;c[8464>>2]=0;i=d;return}if((e|0)==(c[8476>>2]|0)){r=(c[8464>>2]|0)+n|0;c[8464>>2]=r;c[8476>>2]=m;c[m+4>>2]=r|1;c[m+r>>2]=r;i=d;return}r=(w&-8)+n|0;f=w>>>3;do{if(!(w>>>0<256)){k=c[a+(b+24)>>2]|0;g=c[a+(b+12)>>2]|0;do{if((g|0)==(e|0)){o=a+(b+20)|0;l=c[o>>2]|0;if((l|0)==0){t=a+(b+16)|0;s=c[t>>2]|0;if((s|0)==0){x=0;break}else{y=s;z=t}}else{y=l;z=o}while(1){o=y+20|0;l=c[o>>2]|0;if((l|0)!=0){y=l;z=o;continue}o=y+16|0;l=c[o>>2]|0;if((l|0)==0){break}else{y=l;z=o}}if(z>>>0<u>>>0){nb()}else{c[z>>2]=0;x=y;break}}else{o=c[a+(b+8)>>2]|0;if(o>>>0<u>>>0){nb()}l=o+12|0;if((c[l>>2]|0)!=(e|0)){nb()}t=g+8|0;if((c[t>>2]|0)==(e|0)){c[l>>2]=g;c[t>>2]=o;x=g;break}else{nb()}}}while(0);if((k|0)!=0){g=c[a+(b+28)>>2]|0;j=8760+(g<<2)|0;if((e|0)==(c[j>>2]|0)){c[j>>2]=x;if((x|0)==0){c[8460>>2]=c[8460>>2]&~(1<<g);break}}else{if(k>>>0<(c[8472>>2]|0)>>>0){nb()}g=k+16|0;if((c[g>>2]|0)==(e|0)){c[g>>2]=x}else{c[k+20>>2]=x}if((x|0)==0){break}}if(x>>>0<(c[8472>>2]|0)>>>0){nb()}c[x+24>>2]=k;g=c[a+(b+16)>>2]|0;do{if((g|0)!=0){if(g>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[x+16>>2]=g;c[g+24>>2]=x;break}}}while(0);g=c[a+(b+20)>>2]|0;if((g|0)!=0){if(g>>>0<(c[8472>>2]|0)>>>0){nb()}else{c[x+20>>2]=g;c[g+24>>2]=x;break}}}}else{g=c[a+(b+8)>>2]|0;k=c[a+(b+12)>>2]|0;j=8496+(f<<1<<2)|0;if((g|0)!=(j|0)){if(g>>>0<u>>>0){nb()}if((c[g+12>>2]|0)!=(e|0)){nb()}}if((k|0)==(g|0)){c[2114]=c[2114]&~(1<<f);break}if((k|0)!=(j|0)){if(k>>>0<u>>>0){nb()}j=k+8|0;if((c[j>>2]|0)==(e|0)){A=j}else{nb()}}else{A=k+8|0}c[g+12>>2]=k;c[A>>2]=g}}while(0);c[m+4>>2]=r|1;c[m+r>>2]=r;if((m|0)==(c[8476>>2]|0)){c[8464>>2]=r;i=d;return}else{B=r}}else{c[v>>2]=w&-2;c[m+4>>2]=n|1;c[m+n>>2]=n;B=n}n=B>>>3;if(B>>>0<256){w=n<<1;v=8496+(w<<2)|0;r=c[2114]|0;A=1<<n;if((r&A|0)!=0){n=8496+(w+2<<2)|0;e=c[n>>2]|0;if(e>>>0<(c[8472>>2]|0)>>>0){nb()}else{C=n;D=e}}else{c[2114]=r|A;C=8496+(w+2<<2)|0;D=v}c[C>>2]=m;c[D+12>>2]=m;c[m+8>>2]=D;c[m+12>>2]=v;i=d;return}v=B>>>8;if((v|0)!=0){if(B>>>0>16777215){E=31}else{D=(v+1048320|0)>>>16&8;C=v<<D;v=(C+520192|0)>>>16&4;w=C<<v;C=(w+245760|0)>>>16&2;A=14-(v|D|C)+(w<<C>>>15)|0;E=B>>>(A+7|0)&1|A<<1}}else{E=0}A=8760+(E<<2)|0;c[m+28>>2]=E;c[m+20>>2]=0;c[m+16>>2]=0;C=c[8460>>2]|0;w=1<<E;if((C&w|0)==0){c[8460>>2]=C|w;c[A>>2]=m;c[m+24>>2]=A;c[m+12>>2]=m;c[m+8>>2]=m;i=d;return}w=c[A>>2]|0;if((E|0)==31){F=0}else{F=25-(E>>>1)|0}a:do{if((c[w+4>>2]&-8|0)==(B|0)){G=w}else{E=B<<F;A=w;while(1){H=A+(E>>>31<<2)+16|0;C=c[H>>2]|0;if((C|0)==0){break}if((c[C+4>>2]&-8|0)==(B|0)){G=C;break a}else{E=E<<1;A=C}}if(H>>>0<(c[8472>>2]|0)>>>0){nb()}c[H>>2]=m;c[m+24>>2]=A;c[m+12>>2]=m;c[m+8>>2]=m;i=d;return}}while(0);H=G+8|0;B=c[H>>2]|0;w=c[8472>>2]|0;if(G>>>0<w>>>0){nb()}if(B>>>0<w>>>0){nb()}c[B+12>>2]=m;c[H>>2]=m;c[m+8>>2]=B;c[m+12>>2]=G;c[m+24>>2]=0;i=d;return}function Zf(b){b=b|0;var c=0,d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0,o=0,p=0,q=0,r=0;c=i;d=b;while(1){e=d+1|0;if((Ya(a[d]|0)|0)==0){break}else{d=e}}b=a[d]|0;f=b<<24>>24;if((f|0)==45){g=1;h=5}else if((f|0)==43){g=0;h=5}else{j=d;k=b;l=0}if((h|0)==5){j=e;k=a[e]|0;l=g}if((rb(k<<24>>24|0)|0)==0){m=0;n=(l|0)!=0;o=0-m|0;p=n?m:o;i=c;return p|0}else{q=j;r=0}while(1){j=q+1|0;k=(r*10|0)+48-(a[q]|0)|0;if((rb(a[j]|0)|0)==0){m=k;break}else{q=j;r=k}}n=(l|0)!=0;o=0-m|0;p=n?m:o;i=c;return p|0}function _f(b,c,d){b=b|0;c=c|0;d=d|0;var e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0;e=i;a:do{if((d|0)==0){f=0}else{g=d;h=b;j=c;while(1){k=a[h]|0;l=a[j]|0;if(!(k<<24>>24==l<<24>>24)){break}m=g+ -1|0;if((m|0)==0){f=0;break a}else{g=m;h=h+1|0;j=j+1|0}}f=(k&255)-(l&255)|0}}while(0);i=e;return f|0}function $f(b,c){b=b|0;c=c|0;var d=0,e=0,f=0,g=0,h=0,j=0,k=0,l=0,m=0,n=0;d=i;e=a[b]|0;f=a[c]|0;if(e<<24>>24!=f<<24>>24|e<<24>>24==0|f<<24>>24==0){g=e;h=f;j=g&255;k=h&255;l=j-k|0;i=d;return l|0}else{m=b;n=c}while(1){c=m+1|0;b=n+1|0;f=a[c]|0;e=a[b]|0;if(f<<24>>24!=e<<24>>24|f<<24>>24==0|e<<24>>24==0){g=f;h=e;break}else{m=c;n=b}}j=g&255;k=h&255;l=j-k|0;i=d;return l|0}function ag(){}function bg(b){b=b|0;var c=0;c=b;while(a[c]|0){c=c+1|0}return c-b|0}function cg(b,d,e){b=b|0;d=d|0;e=e|0;var f=0,g=0,h=0,i=0;f=b+e|0;if((e|0)>=20){d=d&255;g=b&3;h=d|d<<8|d<<16|d<<24;i=f&~3;if(g){g=b+4-g|0;while((b|0)<(g|0)){a[b]=d;b=b+1|0}}while((b|0)<(i|0)){c[b>>2]=h;b=b+4|0}}while((b|0)<(f|0)){a[b]=d;b=b+1|0}return b-e|0}function dg(b,c){b=b|0;c=c|0;var d=0,e=0;d=b+(bg(b)|0)|0;do{a[d+e|0]=a[c+e|0];e=e+1|0}while(a[c+(e-1)|0]|0);return b|0}function eg(b,d,e){b=b|0;d=d|0;e=e|0;var f=0;if((e|0)>=4096)return Oa(b|0,d|0,e|0)|0;f=b|0;if((b&3)==(d&3)){while(b&3){if((e|0)==0)return f|0;a[b]=a[d]|0;b=b+1|0;d=d+1|0;e=e-1|0}while((e|0)>=4){c[b>>2]=c[d>>2];b=b+4|0;d=d+4|0;e=e-4|0}}while((e|0)>0){a[b]=a[d]|0;b=b+1|0;d=d+1|0;e=e-1|0}return f|0}function fg(b,c,d){b=b|0;c=c|0;d=d|0;var e=0;if((c|0)<(b|0)&(b|0)<(c+d|0)){e=b;c=c+d|0;b=b+d|0;while((d|0)>0){b=b-1|0;c=c-1|0;d=d-1|0;a[b]=a[c]|0}b=e}else{eg(b,c,d)|0}return b|0}function gg(b,c){b=b|0;c=c|0;var d=0;do{a[b+d|0]=a[c+d|0];d=d+1|0}while(a[c+(d-1)|0]|0);return b|0}function hg(a,b,c,d,e){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;return Ab[a&3](b|0,c|0,d|0,e|0)|0}function ig(a,b,c){a=a|0;b=b|0;c=+c;Bb[a&0](b|0,+c)}function jg(a,b,c,d,e,f){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;Cb[a&3](b|0,c|0,d|0,e|0,f|0)}function kg(a){a=a|0;return Db[a&1]()|0}function lg(a,b){a=a|0;b=b|0;Eb[a&7](b|0)}function mg(a,b,c){a=a|0;b=b|0;c=c|0;Fb[a&7](b|0,c|0)}function ng(a,b,c,d,e,f,g){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;g=g|0;return Gb[a&1](b|0,c|0,d|0,e|0,f|0,g|0)|0}function og(a,b,c,d,e,f,g,h){a=a|0;b=b|0;c=+c;d=+d;e=+e;f=+f;g=+g;h=h|0;Hb[a&1](b|0,+c,+d,+e,+f,+g,h|0)}function pg(a,b,c,d,e,f,g,h,i){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;g=g|0;h=+h;i=+i;Ib[a&1](b|0,c|0,d|0,e|0,f|0,g|0,+h,+i)}function qg(a,b){a=a|0;b=b|0;return Jb[a&15](b|0)|0}function rg(a,b,c,d){a=a|0;b=b|0;c=c|0;d=d|0;return Kb[a&7](b|0,c|0,d|0)|0}function sg(a,b,c,d){a=a|0;b=b|0;c=c|0;d=d|0;Lb[a&3](b|0,c|0,d|0)}function tg(a,b,c,d,e,f,g,h,i){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;i=i|0;Mb[a&1](b|0,c|0,d|0,e|0,f|0,g|0,h|0,i|0)}function ug(a,b,c,d,e,f,g){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;g=g|0;Nb[a&3](b|0,c|0,d|0,e|0,f|0,g|0)}function vg(a,b,c){a=a|0;b=b|0;c=c|0;return Ob[a&7](b|0,c|0)|0}function wg(a,b,c,d,e){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;return+Pb[a&3](b|0,c|0,d|0,e|0)}function xg(a,b,c,d,e){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;Qb[a&7](b|0,c|0,d|0,e|0)}function yg(a,b,c,d){a=a|0;b=b|0;c=c|0;d=d|0;_(0);return 0}function zg(a,b){a=a|0;b=+b;_(1)}function Ag(a,b,c,d,e){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;_(2)}function Bg(){_(3);return 0}function Cg(a){a=a|0;_(4)}function Dg(a,b){a=a|0;b=b|0;_(5)}function Eg(a,b,c,d,e,f){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;_(6);return 0}function Fg(a,b,c,d,e,f,g){a=a|0;b=+b;c=+c;d=+d;e=+e;f=+f;g=g|0;_(7)}function Gg(a,b,c,d,e,f,g,h){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;g=+g;h=+h;_(8)}function Hg(a){a=a|0;_(9);return 0}function Ig(a,b,c){a=a|0;b=b|0;c=c|0;_(10);return 0}function Jg(a,b,c){a=a|0;b=b|0;c=c|0;_(11)}function Kg(a,b,c,d,e,f,g,h){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;g=g|0;h=h|0;_(12)}function Lg(a,b,c,d,e,f){a=a|0;b=b|0;c=c|0;d=d|0;e=e|0;f=f|0;_(13)}function Mg(a,b){a=a|0;b=b|0;_(14);return 0}function Ng(a,b,c,d){a=a|0;b=b|0;c=c|0;d=d|0;_(15);return 0.0}function Og(a,b,c,d){a=a|0;b=b|0;c=c|0;d=d|0;_(16)}




// EMSCRIPTEN_END_FUNCS
var Ab=[yg,Be,Ge,yg];var Bb=[zg];var Cb=[Ag,Wc,Yc,Zc];var Db=[Bg,se];var Eb=[Cg,_c,$c,ad,we,Fe,Ke,pd];var Fb=[Dg,bd,dd,ue,Me,Ue,Dg,Dg];var Gb=[Eg,Oe];var Hb=[Fg,hd];var Ib=[Gg,Ve];var Jb=[Hg,xe,ye,ze,Ee,He,Ie,Je,Le,Ye,Hg,Hg,Hg,Hg,Hg,Hg];var Kb=[Ig,cd,gd,te,De,Ig,Ig,Ig];var Lb=[Jg,Ne,Ze,_e];var Mb=[Kg,Tc];var Nb=[Lg,Uc,Vc,Xc];var Ob=[Mg,ve,Ae,Ce,Pe,Se,Te,$e];var Pb=[Ng,We,Xe,Ng];var Qb=[Og,ed,fd,Qe,Re,Og,Og,Og];return{_malloc:Uf,_restore_puzzle_size:Lc,_strcat:dg,_resize_puzzle:Kc,_command:ld,_timer_callback:Jc,_key:Sc,_memmove:fg,_realloc:Wf,_strlen:bg,_memset:cg,_dlg_return_ival:kd,_free:Vf,_mousedown:Oc,_mouseup:Qc,_dlg_return_sval:jd,_mousemove:Rc,_memcpy:eg,_strcpy:gg,_main:od,runPostSets:ag,stackAlloc:Rb,stackSave:Sb,stackRestore:Tb,setThrew:Ub,setTempRet0:Xb,setTempRet1:Yb,setTempRet2:Zb,setTempRet3:_b,setTempRet4:$b,setTempRet5:ac,setTempRet6:bc,setTempRet7:cc,setTempRet8:dc,setTempRet9:ec,dynCall_iiiii:hg,dynCall_vid:ig,dynCall_viiiii:jg,dynCall_i:kg,dynCall_vi:lg,dynCall_vii:mg,dynCall_iiiiiii:ng,dynCall_vidddddi:og,dynCall_viiiiiidd:pg,dynCall_ii:qg,dynCall_iiii:rg,dynCall_viii:sg,dynCall_viiiiiiii:tg,dynCall_viiiiii:ug,dynCall_iii:vg,dynCall_diiii:wg,dynCall_viiii:xg}})


// EMSCRIPTEN_END_ASM
({ "Math": Math, "Int8Array": Int8Array, "Int16Array": Int16Array, "Int32Array": Int32Array, "Uint8Array": Uint8Array, "Uint16Array": Uint16Array, "Uint32Array": Uint32Array, "Float32Array": Float32Array, "Float64Array": Float64Array }, { "abort": abort, "assert": assert, "asmPrintInt": asmPrintInt, "asmPrintFloat": asmPrintFloat, "min": Math_min, "invoke_iiiii": invoke_iiiii, "invoke_vid": invoke_vid, "invoke_viiiii": invoke_viiiii, "invoke_i": invoke_i, "invoke_vi": invoke_vi, "invoke_vii": invoke_vii, "invoke_iiiiiii": invoke_iiiiiii, "invoke_vidddddi": invoke_vidddddi, "invoke_viiiiiidd": invoke_viiiiiidd, "invoke_ii": invoke_ii, "invoke_iiii": invoke_iiii, "invoke_viii": invoke_viii, "invoke_viiiiiiii": invoke_viiiiiiii, "invoke_viiiiii": invoke_viiiiii, "invoke_iii": invoke_iii, "invoke_diiii": invoke_diiii, "invoke_viiii": invoke_viiii, "_js_error_box": _js_error_box, "_js_dialog_cleanup": _js_dialog_cleanup, "_js_select_preset": _js_select_preset, "_js_dialog_init": _js_dialog_init, "_js_canvas_draw_line": _js_canvas_draw_line, "___setErrNo": ___setErrNo, "_js_canvas_find_font_midpoint": _js_canvas_find_font_midpoint, "___assert_fail": ___assert_fail, "___buildEnvironment": ___buildEnvironment, "_js_focus_canvas": _js_focus_canvas, "_js_canvas_set_size": _js_canvas_set_size, "_js_dialog_launch": _js_dialog_launch, "_js_canvas_draw_circle": _js_canvas_draw_circle, "_js_canvas_draw_rect": _js_canvas_draw_rect, "_sscanf": _sscanf, "_sbrk": _sbrk, "_js_dialog_boolean": _js_dialog_boolean, "_js_canvas_new_blitter": _js_canvas_new_blitter, "_snprintf": _snprintf, "___errno_location": ___errno_location, "_emscripten_memcpy_big": _emscripten_memcpy_big, "_js_canvas_make_statusbar": _js_canvas_make_statusbar, "_js_enable_undo_redo": _js_enable_undo_redo, "_sysconf": _sysconf, "_js_canvas_unclip": _js_canvas_unclip, "_js_canvas_draw_poly": _js_canvas_draw_poly, "_js_canvas_draw_text": _js_canvas_draw_text, "_js_dialog_string": _js_dialog_string, "_js_canvas_draw_update": _js_canvas_draw_update, "_js_update_permalinks": _js_update_permalinks, "_isspace": _isspace, "_js_remove_type_dropdown": _js_remove_type_dropdown, "_js_remove_solve_button": _js_remove_solve_button, "_getenv": _getenv, "_sprintf": _sprintf, "_js_canvas_start_draw": _js_canvas_start_draw, "__reallyNegative": __reallyNegative, "_toupper": _toupper, "_js_get_date_64": _js_get_date_64, "_fflush": _fflush, "__scanString": __scanString, "_js_deactivate_timer": _js_deactivate_timer, "_vsnprintf": _vsnprintf, "_js_canvas_copy_from_blitter": _js_canvas_copy_from_blitter, "_js_activate_timer": _js_activate_timer, "_js_canvas_end_draw": _js_canvas_end_draw, "_js_canvas_free_blitter": _js_canvas_free_blitter, "_abort": _abort, "_js_dialog_choices": _js_dialog_choices, "_js_canvas_copy_to_blitter": _js_canvas_copy_to_blitter, "_time": _time, "_isdigit": _isdigit, "_js_canvas_set_statusbar": _js_canvas_set_statusbar, "_js_add_preset": _js_add_preset, "__formatString": __formatString, "_js_canvas_clip_rect": _js_canvas_clip_rect, "_sqrt": _sqrt, "__getFloat": __getFloat, "_js_get_selected_preset": _js_get_selected_preset, "STACKTOP": STACKTOP, "STACK_MAX": STACK_MAX, "tempDoublePtr": tempDoublePtr, "ABORT": ABORT, "NaN": NaN, "Infinity": Infinity }, buffer);
var _malloc = Module["_malloc"] = asm["_malloc"];
var _restore_puzzle_size = Module["_restore_puzzle_size"] = asm["_restore_puzzle_size"];
var _strcat = Module["_strcat"] = asm["_strcat"];
var _resize_puzzle = Module["_resize_puzzle"] = asm["_resize_puzzle"];
var _command = Module["_command"] = asm["_command"];
var _timer_callback = Module["_timer_callback"] = asm["_timer_callback"];
var _key = Module["_key"] = asm["_key"];
var _memmove = Module["_memmove"] = asm["_memmove"];
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
var dynCall_vid = Module["dynCall_vid"] = asm["dynCall_vid"];
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

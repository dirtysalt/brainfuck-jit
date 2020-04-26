#!/usr/bin/env python2

"""Brainf**k JIT-compiler that produces CPython bytecode.
You need the byteplay module to run this.

Note that this VM may not reliably run some example programs. This is probably
because of bugs.  Also, it doesn't implement extended jumps, so some programs
with long jumps will not work with this one.  In particular, it doesn't seem to
run hanoi.bf correctly.

Copyright (C) 2015 Christian Stigen Larsen

Distributed under the LGPL v2.1 or later. You are allowed to change the license
on a particular copy to the LGPL 3.0, the GPL 2.0 or GPL 3.0.
"""

from collections import deque
import os
import sys
from bytecode import Instr as I, Compare, Label, Bytecode


def optimize_source(source, verbose=False):
    if verbose:
        sys.stderr.write("optimizing ... ")
        sys.stderr.flush()

    # Remove header comments
    while source[0] == "[":
        n, count = 1, 1
        while count > 0:
            if source[n] == "[":
                count += 1
            elif source[n] == "]":
                count -= 1
            n += 1
        source = source[n:]

    # Remove unknown operations
    source = filter(lambda x: x in "+-<>.,[]", source)

    # Contract same-operator sequences (e.g. ++++ => op=+ count=4)
    out, prev, count = [], None, 0
    for op in source:
        if (op in "[]") or (op != prev):
            if count > 0:
                out.append((prev, count))
            prev, count = op, 1
        else:
            count += 1
    out.append((prev, count))

    # Optimize [-] to "zero current memory cell"
    n = 0
    while n < len(out) - 2:
        a, ac = out[n]
        b, bc = out[n+1]
        c, cc = out[n+2]
        if a == "[" and b == "-" and bc == 1 and c == "]":
            out[n] = ("zero", 0)
            out[n+1] = (None, 0)
            out[n+2] = (None, 0)
            n += 2
        n += 1

    # bytecode does not have limitation of jump offset should be less than 4096
    # https://bytecode.readthedocs.io/en/latest/byteplay_codetransformer.html#jump-targets

    if verbose:
        sys.stderr.write("\n")
        sys.stderr.write("optimized from %d to %d instructions\n" %
                         (len(source), len(out)))

    return out


def compile(source, flush=True, modulus=None, verbose=False):
    # Bytecode
    c = []

    # Keep track of jump labels
    labels = []
    patches = []

    # needs local variables
    # 1. mem
    # 2. ptr
    # 3. sys_read
    # 4. sys_write
    def add(value):
        codes = [
            I("LOAD_FAST", "mem"),
            I("LOAD_FAST", "ptr"),
            I("DUP_TOP_TWO"),
            I("BINARY_SUBSCR"),
            I("LOAD_CONST", value),
            I("BINARY_ADD"),
            I("LOAD_CONST", 0xff),
            I("BINARY_AND"),
            I("ROT_THREE"),
            I("STORE_SUBSCR"),
        ]
        c.extend(codes)

    def zero():
        codes = [
            I("LOAD_CONST", 0),
            I("LOAD_FAST", "mem"),
            I("LOAD_FAST", "ptr"),
            I("STORE_SUBSCR")
        ]
        c.extend(codes)

    def dot(count):
        codes = [
            I("LOAD_FAST", "sys_write"),
            I("LOAD_FAST", "mem"),
            I("LOAD_FAST", "ptr"),
            I("BINARY_SUBSCR"),
            I("LOAD_CONST", count),
            I("CALL_FUNCTION", 2),
            I("POP_TOP")
        ]
        c.extend(codes)

    def comma(count):
        codes = [
            I("LOAD_FAST", "sys_read"),
            I("LOAD_CONST", count),
            I("CALL_FUNCTION", 1),
            I("LOAD_FAST", "mem"),
            I("LOAD_FAST", "ptr"),
            I("STORE_SUBSCR")
        ]
        c.extend(codes)

    def move(amount):
        codes = [
            I("LOAD_FAST", "ptr"),
            I("LOAD_CONST", amount),
            I("BINARY_ADD"),
            I("STORE_FAST", "ptr"),
        ]
        c.extend(codes)

    def start_loop():
        start_label = Label()
        codes = [
            start_label,
            I("LOAD_FAST", "mem"),
            I("LOAD_FAST", "ptr"),
            I("BINARY_SUBSCR"),
            I("LOAD_CONST", 0),
            I("COMPARE_OP", Compare.EQ),
            None,
        ]
        c.extend(codes)
        labels.append(start_label)
        patches.append(len(c) - 1)

    def end_loop():
        start_label = labels.pop()
        end_label = Label()
        pp = patches.pop()
        c[pp] = I("POP_JUMP_IF_TRUE", end_label)
        codes = [
            end_label,
            I("LOAD_FAST", "mem"),
            I("LOAD_FAST", "ptr"),
            I("BINARY_SUBSCR"),
            I("LOAD_CONST", 0),
            I("COMPARE_OP", Compare.EQ),
            I("POP_JUMP_IF_FALSE", start_label)
        ]
        c.extend(codes)

    # Translate Brainfuck to Python bytecode
    for (op, count) in optimize_source(source, verbose=verbose):
        if op == ">":
            move(count)
        elif op == "<":
            move(-count)
        elif op == "+":
            add(count)
        elif op == "-":
            add(-count)
        elif op == ".":
            dot(count)
        elif op == ",":
            comma(count)
        elif op == "[":
            start_loop()
        elif op == "]":
            end_loop()
        elif op == "zero":
            zero()
        elif op is None:
            pass
        else:
            print("Unknown operator: %s" % op)
            sys.exit(1)

    # return None
    c.append(I("LOAD_CONST", None))
    c.append(I("RETURN_VALUE"))
    return c


def make_function(bytecode):
    def sys_write(c, rep):
        sys.stdout.write(chr(c) * rep)
        sys.stdout.flush()

    def sys_read(rep):
        data = sys.stdin.read(rep)
        return ord(data[-1]) & 0xff

    memsize = 10 ** 6
    mem = [0] * memsize
    ptr = 0

    local_vars = dict(
        mem=mem,
        ptr=ptr,
        sys_read=sys_read,
        sys_write=sys_write
    )

    load_cs = []
    for k in local_vars:
        load_cs.extend([
            I("LOAD_NAME", k),
            I("STORE_FAST", k)
        ])

    # for x in bytecode:
    #     print(x)

    def f():
        code = Bytecode(load_cs + bytecode).to_code()
        exec(code, {}, local_vars)

    return f


if __name__ == "__main__":
    export = False
    flush = True
    modulus = None
    verbose = False

    for arg in sys.argv[1:]:
        if arg == "-e":
            export = True
        elif arg == "-b":
            flush = False
        elif arg == "-u8":
            modulus = 2**8
        elif arg == "-u16":
            modulus = 2**16
        elif arg == "-u32":
            modulus = 2**32
        elif arg == "-v":
            verbose = True

    for filename in sys.argv[1:]:
        if filename[0] == "-":
            continue
        with open(filename, "rt") as file:
            name = os.path.splitext(os.path.basename(filename))[0]

            source = file.read()
            compiled = compile(list(source), flush=flush, modulus=modulus,
                               verbose=verbose)
            program = make_function(compiled)

            if not export:
                program()
            else:
                import marshal
                s = marshal.dumps(program.func_code)
                with open(name + ".marshalled", "wb") as f:
                    f.write(s)

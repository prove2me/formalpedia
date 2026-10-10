-- Prove2me | Theorems.Thm_IntMul_TapeAdder_add_equal_width
-- name    : IntMul.TapeAdder.add_equal_width
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T18:37:50.394739+00:00
-- url     : https://prove2.me/theorems/a10f45f5-8d81-469f-9f0d-5e85d6760cca
-- title:
--   Literal binary addition in 3n+4 actual multitape transitions
-- statement:
--   For every two equal-width binary words x,y of width n, the explicitly defined fixed three-tape machine is halted after exactly 3n+4 actual transitions and its output is exactly bin(n+1,val(x)+val(y)), followed by blanks. This includes empty inputs and arbitrary leading zeroes. The machine has a fixed five-symbol alphabet and six states, uses no oracle or head-position test, and satisfies all campaign-model tape rules. Consequently addition has the milestone’s bound 3n+4 ≤ 4(n+1). Subtraction and multiplication are separate obligations.
-- source:
--   Explicit implementation of the addition half of IntMul.TM.add_sub_linear (https://prove2.me/theorems/02ee99a6-3049-4d13-a20d-ec092f55e29c) for the integer-multiplication κ campaign, using IntMul_MultitapeModel and the elementary Boolean full-adder truth table. The finite transition table is this formalization’s implementation, not a table asserted by a cited paper.

import Definitions.Def_IntMul_TapeAdder
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

theorem IntMul.TapeAdder.add_equal_width (x y : List Bool) (h : x.length = y.length) :
    IntMul.TapeAdder.machine.HaltsWithOutput x y (3 * x.length + 4)
      (IntMul.bin (x.length + 1) (IntMul.val x + IntMul.val y)) := by sorry

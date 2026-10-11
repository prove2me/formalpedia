-- Prove2me | Theorems.Thm_IntMul_ZeroCarry_initialize_zero_carry
-- name    : IntMul.ZeroCarry.initialize_zero_carry
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T16:44:58.435079+00:00
-- url     : https://prove2.me/theorems/af144844-9cde-40a0-bdc6-4d3dde4c237b
-- title:
--   Physical zero-carry generation and marker rewind with a linear clock
-- statement:
--   For every finite binary descriptor $l$, let $N=\operatorname{val}(l)+1$. A fixed four-tape finite controller starts with empty output and two prepared marked copies of $l$, while retaining arbitrary original input cells and head. It generates the canonical $N$-bit zero carry and physically rewinds its output head to the actual marker, reaching its exact final globally halted frame within
--
--   $$7N+4|l|+7$$
--
--   actual transitions. Both countdown/template words are fully restored with their saved cursors; original input cells and head remain unchanged. The final output is $\operatorname{bin}_N(0)$ with head at cell zero. Empty and leading-zero descriptors are allowed. Descriptor preparation and relocation into another carry bank remain separate stages.
-- source:
--   Original physical zero-carry initialization with complete generated payload and real marker rewind. Written by Codex.

import Definitions.Def_IntMul_ZeroCarry
import Mathlib.Tactic

open IntMul IntMul.ZeroCarry

theorem IntMul.ZeroCarry.initialize_zero_carry (base : machine.Cfg) (z : List Bool) :
    ∃ t : ℕ, t≤ 7*(val z+1)+4*z.length+7 ∧
      machine.step^[t] (initialFrame base z)=finalFrame base z ∧
      (machine.step^[t] (initialFrame base z)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base z)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[t] (initialFrame base z)).head machine.inTape=base.head machine.inTape ∧
      (machine.step^[t] (initialFrame base z)).cells machine.outTape=
        machine.tapeOf ((bin (val z+1) 0).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base z)).head machine.outTape=0 := by sorry

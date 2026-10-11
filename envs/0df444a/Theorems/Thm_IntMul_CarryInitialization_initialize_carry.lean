-- Prove2me | Theorems.Thm_IntMul_CarryInitialization_initialize_carry
-- name    : IntMul.CarryInitialization.initialize_carry
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T17:00:02.528017+00:00
-- url     : https://prove2.me/theorems/e853acb2-f213-4cfa-8259-6d16fdec893e
-- title:
--   Physical zero-carry generation and marker rewind with a linear clock
-- statement:
--   For every finite binary descriptor $l$, let $N=\operatorname{val}(l)+1$. A fixed four-tape finite controller starts with empty carry bank 12 and two empty countdown banks 3 and 4, with retained $l$ on bank 15 at its marker, while retaining arbitrary original input cells and head. It generates the canonical $N$-bit zero carry and physically rewinds its output head to the actual marker, reaching its exact final globally halted frame within
--
--   $$7N+6|l|+13$$
--
--   actual transitions. Both countdown/template words are fully restored with their saved cursors; original input cells and head remain unchanged. The final carry bank 12 is $\operatorname{bin}_N(0)$ with head at cell zero. Empty and leading-zero descriptors are allowed. Both descriptor copies are prepared physically. Relocation into a different bank remains a separate stage.
-- source:
--   Original physical zero-carry initialization with complete generated payload and real marker rewind. Written by Codex.

import Definitions.Def_IntMul_CarryInitialization
import Mathlib.Tactic

open IntMul IntMul.CarryInitialization

theorem IntMul.CarryInitialization.initialize_carry (base : machine.Cfg) (l : List Bool) :
    ∃ t : ℕ, t≤ 7*(val l+1)+6*l.length+13 ∧
      machine.step^[t] (initialFrame base l)=finalFrame base l ∧
      (machine.step^[t] (initialFrame base l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base l)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[t] (initialFrame base l)).head machine.inTape=base.head machine.inTape ∧
      (machine.step^[t] (initialFrame base l)).cells 12=machine.tapeOf ((bin (val l+1) 0).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base l)).head 12=0 ∧
      (machine.step^[t] (initialFrame base l)).cells 15=machine.tapeOf (l.map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base l)).head 15=0 ∧
      (∀ i : Fin 16, i.val≠3 → i.val≠4 → i.val≠12 → i.val≠15 →
        (machine.step^[t] (initialFrame base l)).cells i=base.cells i ∧
        (machine.step^[t] (initialFrame base l)).head i=base.head i) := by sorry

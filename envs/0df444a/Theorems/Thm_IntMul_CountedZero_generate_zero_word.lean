-- Prove2me | Theorems.Thm_IntMul_CountedZero_generate_zero_word
-- name    : IntMul.CountedZero.generate_zero_word
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T16:31:48.978705+00:00
-- url     : https://prove2.me/theorems/25e4ba17-2a43-4ba8-80cb-d7879e04f45a
-- title:
--   Actual zero-carry initialization from binary countdown templates with a linear clock
-- statement:
--   Let $l$ be any finite binary word and put $N=\operatorname{val}(l)+1$. A fixed four-tape machine starts with an empty output at its marker and two physically prepared copies of the marked countdown word $l$. The original input cells and head come from an arbitrary caller frame. Without a supplied zero payload, it globally halts in its exact final frame within
--
--   $$6N+4|l|+3$$
--
--   actual transitions, with output exactly $\operatorname{bin}_N(0)$ and the output cursor at $N+1$. Both countdown and saved template are fully restored, with heads at their original descriptor-end cursors. Original input cells and head are retained. Empty descriptor words and leading zeros are allowed. Descriptor preparation and physical return of the generated word to another bank remain separate caller stages.
-- source:
--   Original complete physical binary-counted zero-word generator and exact retained frame. Written by Codex.

import Definitions.Def_IntMul_CountedStream
import Mathlib.Tactic
import Definitions.Def_IntMul_CountedZero
import Mathlib.Data.List.GetD

open IntMul IntMul.CountedZero

theorem IntMul.CountedZero.generate_zero_word (base : machine.Cfg) (z : List Bool) :
    ∃ t : ℕ, t≤ 6*(val z+1)+4*z.length+3 ∧
      machine.step^[t] (initialFrame base z)=finalFrame base z ∧
      (machine.step^[t] (initialFrame base z)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[t] (initialFrame base z)).head machine.inTape=base.head machine.inTape ∧
      (machine.step^[t] (initialFrame base z)).cells machine.outTape=
        machine.tapeOf ((bin (val z+1) 0).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base z)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base z)).head machine.outTape=val z+2 := by sorry

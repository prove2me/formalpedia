-- Prove2me | Theorems.Thm_IntMul_InputWidthPreparation_input_width_preparation
-- name    : IntMul.InputWidthPreparation.input_width_preparation
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T15:00:33.711515+00:00
-- url     : https://prove2.me/theorems/72d47f60-793a-477c-9681-07e048db978c
-- title:
--   Complete retained width and countdown initialization from original operand input with linear clock
-- statement:
--   Let $x,y$ be binary operand words with $W=|x|+|y|>0$. A fixed sixteen-tape machine starts from the ordinary initial configuration on $x\#y$, with empty work tapes and all heads on their real start markers. It physically computes and retains a big-endian word $d$ satisfying
--
--   $$\operatorname{val}(d)+1=W,$$
--
--   and writes both delimited countdown copies $\#d\#$ at their least-significant-bit cursors. It globally halts in its exact terminal configuration within
--
--   $$18W+21$$
--
--   actual transitions. The original input is retained read-only, global output remains empty and all unused scratch banks remain empty. The retained descriptor is rewound to its actual start marker. No width or counter word is supplied in advance. This completes the input-derived physical width and countdown preparation required by exact padded multiplication output.
-- source:
--   Original complete retained width and countdown preparation from true initialization; all computation, rewinds, copies and returns charged. Written by Codex.

import Definitions.Def_IntMul_InputWidthPreparation
import Mathlib.Tactic

open IntMul IntMul.InputWidthPreparation

theorem IntMul.InputWidthPreparation.input_width_preparation (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 18*(x.length+y.length)+21 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=machine.tapeOf [] ∧
      val (CanonicalWidthDescriptor.descriptorWord x y)+1=x.length+y.length := by sorry

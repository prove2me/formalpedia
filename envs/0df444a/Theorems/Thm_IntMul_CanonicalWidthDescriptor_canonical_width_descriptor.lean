-- Prove2me | Theorems.Thm_IntMul_CanonicalWidthDescriptor_canonical_width_descriptor
-- name    : IntMul.CanonicalWidthDescriptor.canonical_width_descriptor
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T14:52:56.107034+00:00
-- url     : https://prove2.me/theorems/1c42bfd8-e14b-4eb4-8791-dcbde495cfa0
-- title:
--   Complete input-derived canonical width descriptor from global initialization with linear clock
-- statement:
--   Let $x,y$ be binary operand words with $W=|x|+|y|>0$. One fixed fifteen-tape machine starts from the ordinary initial configuration on $x\#y$, with every work tape empty and every head at its start marker. It physically constructs a finite big-endian descriptor $d$ satisfying
--
--   $$\operatorname{val}(d)+1=W,$$
--
--   and halts in its exact complete terminal configuration after at most
--
--   $$15W+15$$
--
--   actual transitions. Output contains exactly $d$, the original input is retained read-only and every scratch bank is empty. No width word or length is supplied in advance. The theorem includes the actual binary count, source scans, counter growth, marker rewinds, physical seek to the counter blank, output reversal, scratch erasures and every caller return. It provides the input-derived width descriptor required for exact padded multiplication output.
-- source:
--   Original complete global-initial width descriptor calculation and physical canonicalization. Written by Codex.

import Definitions.Def_IntMul_CanonicalWidthDescriptor
import Mathlib.Tactic

open IntMul IntMul.CanonicalWidthDescriptor

theorem IntMul.CanonicalWidthDescriptor.canonical_width_descriptor (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 15*(x.length+y.length)+15 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=
        machine.tapeOf ((descriptorWord x y).map machine.bitSym) ∧
      val (descriptorWord x y)+1=x.length+y.length := by sorry

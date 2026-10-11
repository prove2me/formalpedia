-- Prove2me | Theorems.Thm_IntMul_InputBlockDescriptors_input_block_descriptors
-- name    : IntMul.InputBlockDescriptors.input_block_descriptors
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T15:28:06.140171+00:00
-- url     : https://prove2.me/theorems/b70cf5a8-310f-49b7-9eb2-1bb351d61cb8
-- title:
--   Complete original-input width and logarithmic block descriptors with charged global preparation
-- statement:
--   Let $x,y$ be binary operand words with $W=|x|+|y|>0$, and put $\lg W=\max(\lceil\log_2 W\rceil,1)$. A fixed seventeen-tape machine starts from the ordinary initial configuration on $x\#y$, with empty work tapes and all heads at their real start markers. It physically computes retained big-endian descriptors $d,z$ satisfying
--
--   $$\operatorname{val}(d)+1=W,\qquad\operatorname{val}(z)+1=\lg W.$$
--
--   Their exact representation lengths are
--
--   $$|d|=\lceil\log_2 W\rceil,\qquad|z|=\lceil\log_2(\lg W)\rceil.$$
--
--   The machine globally halts in its exact terminal configuration within
--
--   $$18W+7\lceil\log_2 W\rceil+10\lceil\log_2(\lg W)\rceil+50$$
--
--   actual transitions. Original input is retained read-only, global output remains empty, both retained descriptors are at their actual start markers, and both delimited countdown copies of $d$ remain at their least-significant-bit cursors. Every temporary bank is empty at its marker. No width, length or block-size descriptor is supplied in advance. This constructs the real width and positive logarithmic block-size parameters required for later coefficient arithmetic.
-- source:
--   Original complete global preparation of width and logarithmic block-size descriptors, with every scan, copy, counter increment, order conversion, rewind, erasure and return charged. Written by Codex.

import Definitions.Def_IntMul_InputBlockDescriptors
import Mathlib.Tactic

open IntMul IntMul.InputBlockDescriptors

theorem IntMul.InputBlockDescriptors.input_block_descriptors (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 18*(x.length+y.length)+7*Nat.clog 2 (x.length+y.length)+
        10*Nat.clog 2 (lg (x.length+y.length))+50 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=machine.tapeOf [] ∧
      val (widthWord x y)+1=x.length+y.length ∧
      val (blockWord x y)+1=lg (x.length+y.length) ∧
      (widthWord x y).length=Nat.clog 2 (x.length+y.length) ∧
      (blockWord x y).length=Nat.clog 2 (lg (x.length+y.length)) := by sorry

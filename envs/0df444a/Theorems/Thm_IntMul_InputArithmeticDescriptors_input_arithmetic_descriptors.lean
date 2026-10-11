-- Prove2me | Theorems.Thm_IntMul_InputArithmeticDescriptors_input_arithmetic_descriptors
-- name    : IntMul.InputArithmeticDescriptors.input_arithmetic_descriptors
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T16:08:02.160216+00:00
-- url     : https://prove2.me/theorems/6f8a2ce0-c9b2-4d1b-8a9e-719861cf3629
-- title:
--   All physical arithmetic descriptors from the original input with a linear transition bound
-- statement:
--   Let $x,y$ be binary operands and $W=|x|+|y|>0$. A fixed eighteen-tape machine starts from the original input $x\#y$, with all other tapes empty, and halts in its exact final frame within
--
--   $$18W+7\lceil\log_2 W\rceil+21\lceil\log_2(\lg W)\rceil+94\le46W+94$$
--
--   actual transitions. It preserves the original input, leaves global output empty, and retains three big-endian words $d,z,l$ with all three heads at their actual markers, satisfying
--
--   $$\operatorname{val}(d)+1=W,\qquad\operatorname{val}(z)+1=\lg W,\qquad\operatorname{val}(l)+1=3\lg W.$$
--
--   Their lengths obey $|d|=\lceil\log_2 W\rceil$, $|z|=\lceil\log_2(\lg W)\rceil$, and $|l|\le\lceil\log_2(\lg W)\rceil+2$. In particular $|z|\le\lg W$ and $|l|\le3\lg W$. Both physical countdown copies of $d$ are retained in their prepared banks. No descriptor or numerical length is supplied by the caller. All scans, affine carry steps, reversal, marker rewind and caller returns are charged.
-- source:
--   Original physical input-derived arithmetic descriptor setup, exact retained frame and linear clock. Written by Codex.

import Definitions.Def_IntMul_InputArithmeticDescriptors
import Mathlib.Tactic

open IntMul IntMul.InputArithmeticDescriptors

theorem IntMul.InputArithmeticDescriptors.input_arithmetic_descriptors (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 18*(x.length+y.length)+7*Nat.clog 2 (x.length+y.length)+
        21*Nat.clog 2 (lg (x.length+y.length))+94 ∧
      t≤ 46*(x.length+y.length)+94 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=machine.tapeOf [] ∧
      val (widthWord x y)+1=x.length+y.length ∧
      val (blockWord x y)+1=lg (x.length+y.length) ∧
      val (precisionWord x y)+1=3*lg (x.length+y.length) ∧
      (widthWord x y).length=Nat.clog 2 (x.length+y.length) ∧
      (blockWord x y).length=Nat.clog 2 (lg (x.length+y.length)) ∧
      (precisionWord x y).length≤ Nat.clog 2 (lg (x.length+y.length))+2 ∧
      (blockWord x y).length≤ lg (x.length+y.length) ∧
      (precisionWord x y).length≤ 3*lg (x.length+y.length) := by sorry

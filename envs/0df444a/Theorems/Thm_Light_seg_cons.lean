-- Prove2me | Theorems.Thm_Light_seg_cons
-- name    : Light.seg_cons
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:32:39.454093+00:00
-- url     : https://prove2.me/theorems/67ee68f5-e63c-40d4-935d-03250600ef2d
-- title:
--   Splitting the head of a stored memory segment
-- statement:
--   Let $\mu:\mathbb N\to\mathbb Z$ be memory, $a$ a starting address, $x\in\mathbb Z$, and $L$ a list of integers. Write $\operatorname{Seg}(\mu,a,L)$ when memory at addresses $a+i$ contains $L_i$ for every $i<|L|$. Then
--
--   $$\operatorname{Seg}(\mu,a,x::L)\iff\mu(a)=x\;\land\;\operatorname{Seg}(\mu,a+1,L).$$
--
--   This gives the head-and-tail rule for reading or constructing contiguous memory representations.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L65-L77

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSumApsp
end ThreeSumApsp

theorem Light.seg_cons : ∀ {μ : Nat → Int} {a : Nat} {l : List.{0} Int} {x : Int},
  Iff (Light.Seg μ a (@List.cons.{0} Int x l))
    (And (@Eq.{1} Int (μ a) x)
      (Light.Seg μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        l)) := by
  sorry

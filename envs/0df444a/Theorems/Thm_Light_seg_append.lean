-- Prove2me | Theorems.Thm_Light_seg_append
-- name    : Light.seg_append
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:32:56.575147+00:00
-- url     : https://prove2.me/theorems/d25274d7-03e8-45dc-bcf7-1b443f3d15d9
-- title:
--   Concatenation corresponds to adjacent memory segments
-- statement:
--   Let $\mu:\mathbb N\to\mathbb Z$ be memory, $a\in\mathbb N$ an address, and $L_1,L_2$ lists of integers. The predicate $\operatorname{Seg}(\mu,a,L)$ means that memory contains $L$ consecutively from address $a$. Then
--
--   $$\operatorname{Seg}(\mu,a,L_1\mathbin{+\!+}L_2)\iff\operatorname{Seg}(\mu,a,L_1)\land\operatorname{Seg}(\mu,a+|L_1|,L_2).$$
--
--   This equivalence allows a contiguous array representation to be split at a list boundary or assembled from adjacent pieces, including empty pieces.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L79-L93

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

theorem Light.seg_append : ∀ {μ : Nat → Int} {a : Nat} {l₁ l₂ : List.{0} Int},
  Iff
    (Light.Seg μ a
      (@HAppend.hAppend.{0, 0, 0} (List.{0} Int) (List.{0} Int) (List.{0} Int)
        (@instHAppendOfAppend.{0} (List.{0} Int) (@List.instAppend.{0} Int)) l₁ l₂))
    (And (Light.Seg μ a l₁)
      (Light.Seg μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a (@List.length.{0} Int l₁)) l₂)) := by
  sorry

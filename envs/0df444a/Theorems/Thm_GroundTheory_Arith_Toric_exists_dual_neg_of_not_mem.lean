-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_exists_dual_neg_of_not_mem
-- name    : GroundTheory.Arith.Toric.exists_dual_neg_of_not_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:34.714454+00:00
-- url     : https://prove2.me/theorems/41c25641-52bf-4300-9f28-4f6ece9419dc
-- title:
--   Toric: exists dual neg of not mem
-- statement:
--   The Toric construction uses the exists dual neg of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L87-L91

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

theorem GroundTheory.Arith.Toric.exists_dual_neg_of_not_mem {C : PointedCone 𝕜 V} (hC : C.FG) {x : V} (hx : x ∉ C) :
    ∃ f : Dual 𝕜 V, (∀ y ∈ C, 0 ≤ f y) ∧ f x < 0 := by sorry

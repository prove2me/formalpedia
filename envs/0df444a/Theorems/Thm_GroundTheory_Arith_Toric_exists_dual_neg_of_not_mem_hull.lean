-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_exists_dual_neg_of_not_mem_hull
-- name    : GroundTheory.Arith.Toric.exists_dual_neg_of_not_mem_hull
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:27.591704+00:00
-- url     : https://prove2.me/theorems/b52413a1-9985-40b9-9722-766b5f90a379
-- title:
--   Toric: exists dual neg of not mem hull
-- statement:
--   The Toric construction uses the exists dual neg of not mem hull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L42-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L42-L81

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

theorem GroundTheory.Arith.Toric.exists_dual_neg_of_not_mem_hull {ι : Type*} (s : Finset ι) (v : ι → V) {x : V}
    (hx : x ∉ hull 𝕜 (v '' s)) : ∃ f : Dual 𝕜 V, (∀ i ∈ s, 0 ≤ f (v i)) ∧ f x < 0 := by sorry

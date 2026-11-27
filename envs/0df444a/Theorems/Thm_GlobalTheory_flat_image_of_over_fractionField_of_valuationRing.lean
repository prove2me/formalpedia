-- Prove2me | Theorems.Thm_GlobalTheory_flat_image_of_over_fractionField_of_valuationRing
-- name    : GlobalTheory.flat_image_of_over_fractionField_of_valuationRing
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:51.134584+00:00
-- url     : https://prove2.me/theorems/4bd62c80-ab00-47e6-bd36-24b91e08d5a5
-- title:
--   Global Theory: flat image of over fraction Field of valuation Ring
-- statement:
--   The Global Theory construction uses the flat image of over fraction Field of valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L261-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L261-L267

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
variable {W P T' T Z : Scheme.{u}} (j : W ⟶ P)

theorem GlobalTheory.flat_image_of_over_fractionField_of_valuationRing {O K : Type u} [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (s : P ⟶ Spec (.of O))
    (s' : W ⟶ Spec (.of K))
    (h : s' ≫ Spec.map (CommRingCat.ofHom (algebraMap O K)) = j ≫ s) [QuasiCompact j] :
    Flat (j.imageι ≫ s) := by sorry

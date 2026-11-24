-- Prove2me | Theorems.Thm_GlobalTheory_flat_image_of_valuationRing
-- name    : GlobalTheory.flat_image_of_valuationRing
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:52:00.06796+00:00
-- url     : https://prove2.me/theorems/c8c961a7-7e38-4fc0-b6ac-8555769a94bc
-- title:
--   Global Theory: flat image of valuation Ring
-- statement:
--   The Global Theory construction uses the flat image of valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L250-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L250-L252

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

theorem GlobalTheory.flat_image_of_valuationRing {O : CommRingCat.{u}} [IsDomain O] [ValuationRing O]
    (s : P ⟶ Spec O) [QuasiCompact j] [Flat (j ≫ s)] : Flat (j.imageι ≫ s) := by sorry

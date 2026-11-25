-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_closureLift_of_injective
-- name    : GlobalTheory.existsUnique_closureLift_of_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:36.033713+00:00
-- url     : https://prove2.me/theorems/72d56c29-aa3b-4d2f-ad08-a11014cc2115
-- title:
--   Global Theory: exists Unique closure Lift of injective
-- statement:
--   The Global Theory construction uses the exists Unique closure Lift of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L176-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L176-L180

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

theorem GlobalTheory.existsUnique_closureLift_of_injective {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (hφ : Function.Injective φ.hom) (t : Spec R ⟶ P) (w : Spec R' ⟶ W)
    (h : Spec.map φ ≫ t = w ≫ j) : ∃! l : Spec R ⟶ j.image, l ≫ j.imageι = t := by sorry

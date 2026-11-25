-- Prove2me | Theorems.Thm_GlobalTheory_StarTensor_map_star_of
-- name    : GlobalTheory.StarTensor.map_star_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:54.047376+00:00
-- url     : https://prove2.me/theorems/4b7b45c4-bb50-58be-bb20-2e8ed4b1991a
-- title:
--   Star Tensor: map star of
-- statement:
--   The Star Tensor construction uses the map star of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L744-L749
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L744-L749

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
open GlobalTheory
universe u v
attribute [instance] HermModule.addCommGroup HermModule.module
attribute [instance] HermSpace.addCommGroup HermSpace.module HermSpace.finite
attribute [simp] IsStarFixed.star_algebraMap
open GlobalTheory.StarTensor
variable {F E A : Type*} [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]
  [StarRing E] [IsStarFixed F E]

theorem GlobalTheory.StarTensor.map_star_of {C : Type*} [CommRing C] [StarRing C] (φ : StarTensor F E A →+* C)
    (hE : ∀ e, φ (algebraMap E _ (star e)) = star (φ (algebraMap E _ e)))
    (hA : ∀ a, star (φ (algebraMap A _ a)) = φ (algebraMap A _ a)) (x : StarTensor F E A) :
    φ (star x) = star (φ x) := by sorry

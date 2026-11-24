-- Prove2me | Theorems.Thm_GlobalTheory_StarTensor_algebraMap_right_injective
-- name    : GlobalTheory.StarTensor.algebraMap_right_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:22:33.901442+00:00
-- url     : https://prove2.me/theorems/21597104-6bb4-4729-88a4-256b9e0a3c3b
-- title:
--   Star Tensor: algebra Map right injective
-- statement:
--   The Star Tensor construction uses the algebra Map right injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L658-L660
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L658-L660

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
variable (F E A : Type*) [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]
variable {F E A}

theorem GlobalTheory.StarTensor.algebraMap_right_injective [Module.Flat F A] (hE : Function.Injective (algebraMap F E)) :
    Function.Injective (algebraMap A (StarTensor F E A)) := by sorry

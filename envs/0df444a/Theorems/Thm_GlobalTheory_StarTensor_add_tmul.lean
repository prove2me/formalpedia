-- Prove2me | Theorems.Thm_GlobalTheory_StarTensor_add_tmul
-- name    : GlobalTheory.StarTensor.add_tmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:22:38.273438+00:00
-- url     : https://prove2.me/theorems/e46ef31d-4bae-4092-a1bd-766ce3e554b5
-- title:
--   Star Tensor: add tmul
-- statement:
--   The Star Tensor construction uses the add tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L587-L588
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L587-L588

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

theorem GlobalTheory.StarTensor.add_tmul (e e' : E) (a : A) : tmul F (e + e') a = tmul F e a + tmul F e' a := by sorry

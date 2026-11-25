-- Prove2me | Theorems.Thm_GlobalTheory_StarTensor_tmul_add
-- name    : GlobalTheory.StarTensor.tmul_add
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:56.402108+00:00
-- url     : https://prove2.me/theorems/9c00593b-a0d8-5c08-8f1f-e339e841e05b
-- title:
--   Star Tensor: tmul add
-- statement:
--   The Star Tensor construction uses the tmul add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L590-L591
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L590-L591

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

theorem GlobalTheory.StarTensor.tmul_add (e : E) (a a' : A) : tmul F e (a + a') = tmul F e a + tmul F e a' := by sorry

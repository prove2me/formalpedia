-- Prove2me | Theorems.Thm_GlobalTheory_StarTensor_tmul_eq_mul
-- name    : GlobalTheory.StarTensor.tmul_eq_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:22:17.06451+00:00
-- url     : https://prove2.me/theorems/d0f3110b-3b45-4ec0-a0ee-e428c8ff58b3
-- title:
--   Star Tensor: tmul eq mul
-- statement:
--   The Star Tensor construction uses the tmul eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L583-L585
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L583-L585

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

theorem GlobalTheory.StarTensor.tmul_eq_mul (e : E) (a : A) :
    tmul F e a = algebraMap E (StarTensor F E A) e * algebraMap A (StarTensor F E A) a := by sorry

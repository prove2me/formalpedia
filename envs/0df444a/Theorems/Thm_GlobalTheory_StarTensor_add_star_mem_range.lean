-- Prove2me | Theorems.Thm_GlobalTheory_StarTensor_add_star_mem_range
-- name    : GlobalTheory.StarTensor.add_star_mem_range
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:21:59.201796+00:00
-- url     : https://prove2.me/theorems/f1054e26-eb6e-46cc-a156-b2878cefc472
-- title:
--   Star Tensor: add star mem range
-- statement:
--   The Star Tensor construction uses the add star mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L765-L772
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L765-L772

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
variable {B : Type*} [CommRing B] [Algebra F B]

theorem GlobalTheory.StarTensor.add_star_mem_range (hE : ∀ e : E, e + star e ∈ (algebraMap F E).range)
    (x : StarTensor F E A) : x + star x ∈ (algebraMap A (StarTensor F E A)).range := by sorry

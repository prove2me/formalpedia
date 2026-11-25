-- Prove2me | Theorems.Thm_GlobalTheory_StarTensor_lift_star
-- name    : GlobalTheory.StarTensor.lift_star
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:26.316364+00:00
-- url     : https://prove2.me/theorems/18af6f01-423b-5856-a63c-e2ca5f42cc0d
-- title:
--   Star Tensor: lift star
-- statement:
--   The Star Tensor construction uses the lift star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L756-L759
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L756-L759

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

theorem GlobalTheory.StarTensor.lift_star {D : Type*} [CommRing D] [StarRing D] (f : E →+* D) (g : A →+* D) (hfg)
    (hf : ∀ e, f (star e) = star (f e)) (hg : ∀ a, star (g a) = g a)
    (x : StarTensor F E A) : lift f g hfg (star x) = star (lift f g hfg x) := by sorry

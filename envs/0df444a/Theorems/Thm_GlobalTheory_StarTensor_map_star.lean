-- Prove2me | Theorems.Thm_GlobalTheory_StarTensor_map_star
-- name    : GlobalTheory.StarTensor.map_star
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:39.06393+00:00
-- url     : https://prove2.me/theorems/5046b51c-4f2b-45e4-bfa1-bdc86e53d3fc
-- title:
--   Star Tensor: map star
-- statement:
--   The Star Tensor construction uses the map star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L753-L754
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L753-L754

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

theorem GlobalTheory.StarTensor.map_star (f : A →ₐ[F] B) (x : StarTensor F E A) : map E f (star x) = star (map E f x) := by sorry

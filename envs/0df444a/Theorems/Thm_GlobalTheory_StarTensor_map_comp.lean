-- Prove2me | Theorems.Thm_GlobalTheory_StarTensor_map_comp
-- name    : GlobalTheory.StarTensor.map_comp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:29.142203+00:00
-- url     : https://prove2.me/theorems/aa4acc48-5af5-50db-9d11-f28e94ae9446
-- title:
--   Star Tensor: map comp
-- statement:
--   The Star Tensor construction uses the map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L678-L681
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L678-L681

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
variable {B C : Type*} [CommRing B] [CommRing C] [Algebra F B] [Algebra F C]

theorem GlobalTheory.StarTensor.map_comp (g : B →ₐ[F] C) (f : A →ₐ[F] B) :
    map E (g.comp f) = (map E g).comp (map E f) := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_IsStarFixed_isIntegral_star
-- name    : GlobalTheory.IsStarFixed.isIntegral_star
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:09.583706+00:00
-- url     : https://prove2.me/theorems/1ab7fa48-45c0-5960-b967-6e7e3483e1d1
-- title:
--   Is Star Fixed: is Integral star
-- statement:
--   The Is Star Fixed construction uses the is Integral star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L492-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L492-L494

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

theorem GlobalTheory.IsStarFixed.isIntegral_star {F E : Type*} [CommRing F] [CommRing E] [StarRing E]
    [Algebra F E] [IsStarFixed F E] {x : E} (hx : IsIntegral F x) : IsIntegral F (star x) := by sorry

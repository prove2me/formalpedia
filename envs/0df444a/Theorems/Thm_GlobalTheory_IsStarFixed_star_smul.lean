-- Prove2me | Theorems.Thm_GlobalTheory_IsStarFixed_star_smul
-- name    : GlobalTheory.IsStarFixed.star_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:22:15.559339+00:00
-- url     : https://prove2.me/theorems/ef41a4cc-b22c-4d94-b90f-76d1f35f0396
-- title:
--   Is Star Fixed: star smul
-- statement:
--   The Is Star Fixed construction uses the star smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L487-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L487-L488

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
variable (F E : Type*) [CommSemiring F] [CommSemiring E] [StarRing E] [Algebra F E]
variable [IsStarFixed F E]
variable {F E}

theorem GlobalTheory.IsStarFixed.star_smul (a : F) (x : E) : star (a • x) = a • star x := by sorry

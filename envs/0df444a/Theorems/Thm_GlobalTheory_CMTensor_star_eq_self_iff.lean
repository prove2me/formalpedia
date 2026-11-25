-- Prove2me | Theorems.Thm_GlobalTheory_CMTensor_star_eq_self_iff
-- name    : GlobalTheory.CMTensor.star_eq_self_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:58:20.989527+00:00
-- url     : https://prove2.me/theorems/c8910c2a-a11b-4800-a87a-4b5ff6efa423
-- title:
--   CMTensor: star eq self iff
-- statement:
--   The CMTensor construction uses the star eq self iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L907-L917
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L907-L917

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
variable (E : Type*) [Field E] [NumberField E] [IsCMField E]
variable {E}
open GlobalTheory.CMTensor
variable {A : Type*} [CommRing A] [Algebra (maximalRealSubfield E) A]

theorem GlobalTheory.CMTensor.star_eq_self_iff (x : CMTensor E A) :
    star x = x ↔ x ∈ (algebraMap A (CMTensor E A)).range := by sorry

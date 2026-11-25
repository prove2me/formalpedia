-- Prove2me | Theorems.Thm_GlobalTheory_ringOfIntegers_star_eq_self_iff
-- name    : GlobalTheory.ringOfIntegers_star_eq_self_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:03.913196+00:00
-- url     : https://prove2.me/theorems/b9d05856-4117-5b19-ab74-2cceb54e87ec
-- title:
--   Global Theory: ring Of Integers star eq self iff
-- statement:
--   The Global Theory construction uses the ring Of Integers star eq self iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L860-L862
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L860-L862

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

theorem GlobalTheory.ringOfIntegers_star_eq_self_iff (x : 𝓞 E) :
    star x = x ↔ x ∈ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)).range := by sorry

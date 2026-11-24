-- Prove2me | Theorems.Thm_GlobalTheory_ringOfIntegers_coe_star
-- name    : GlobalTheory.ringOfIntegers_coe_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:42.780219+00:00
-- url     : https://prove2.me/theorems/8e832f64-169e-47ea-8c08-17033aca715c
-- title:
--   Global Theory: ring Of Integers coe star
-- statement:
--   The Global Theory construction uses the ring Of Integers coe star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L844-L845
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L844-L845

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

theorem GlobalTheory.ringOfIntegers_coe_star (x : 𝓞 E) :
    algebraMap (𝓞 E) E (star x) = star (algebraMap (𝓞 E) E x) := by sorry

attribute [defeq] GlobalTheory.ringOfIntegers_coe_star

-- Prove2me | Theorems.Thm_GlobalTheory_ringOfIntegers_star_def
-- name    : GlobalTheory.ringOfIntegers_star_def
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:57.416462+00:00
-- url     : https://prove2.me/theorems/546e2109-018b-5377-9bb3-71e635a4f29e
-- title:
--   Global Theory: ring Of Integers star def
-- statement:
--   The Global Theory construction uses the ring Of Integers star def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L842-L842
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L842-L842

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

theorem GlobalTheory.ringOfIntegers_star_def (x : 𝓞 E) : star x = IsCMField.ringOfIntegersComplexConj E x := by sorry

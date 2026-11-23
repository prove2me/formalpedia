-- Prove2me | Theorems.Thm_GlobalTheory_star_eq_self_iff_mem
-- name    : GlobalTheory.star_eq_self_iff_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:34.552886+00:00
-- url     : https://prove2.me/theorems/02692536-6bba-4f5f-9710-f7774ea261df
-- title:
--   Global Theory: star eq self iff mem
-- statement:
--   The Global Theory construction uses the star eq self iff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L817-L818
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L817-L818

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

theorem GlobalTheory.star_eq_self_iff_mem (x : E) : star x = x ↔ x ∈ maximalRealSubfield E := by sorry

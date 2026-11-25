-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_apply_self_mem
-- name    : GlobalTheory.HermForm.apply_self_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:18.545126+00:00
-- url     : https://prove2.me/theorems/4cd73eae-2e64-4ee3-a161-bf1edab5e810
-- title:
--   Herm Form: apply self mem
-- statement:
--   The Herm Form construction uses the apply self mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L832-L834
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L832-L834

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

theorem GlobalTheory.HermForm.apply_self_mem {V : Type*} [AddCommGroup V] [Module E V] (h : HermForm E V)
    (x : V) : h x x ∈ maximalRealSubfield E := by sorry

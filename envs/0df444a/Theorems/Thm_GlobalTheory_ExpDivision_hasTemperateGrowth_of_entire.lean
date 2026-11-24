-- Prove2me | Theorems.Thm_GlobalTheory_ExpDivision_hasTemperateGrowth_of_entire
-- name    : GlobalTheory.ExpDivision.hasTemperateGrowth_of_entire
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:07:32.374828+00:00
-- url     : https://prove2.me/theorems/440ad092-4418-4fdf-8e5f-245e20a7010e
-- title:
--   Exp Division: has Temperate Growth of entire
-- statement:
--   The Exp Division construction uses the has Temperate Growth of entire property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L59-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L59-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision

theorem GlobalTheory.ExpDivision.hasTemperateGrowth_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ R → ‖F z‖ ≤ C) :
    (fun t : ℝ => F t).HasTemperateGrowth := by sorry

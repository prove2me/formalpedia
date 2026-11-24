-- Prove2me | Theorems.Thm_GlobalTheory_ExpDivision_hasTemperateGrowth_div
-- name    : GlobalTheory.ExpDivision.hasTemperateGrowth_div
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:07:20.200287+00:00
-- url     : https://prove2.me/theorems/587b4752-7a94-452e-9232-185169daf08a
-- title:
--   Exp Division: has Temperate Growth div
-- statement:
--   The Exp Division construction uses the has Temperate Growth div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L29-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L29-L57

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

theorem GlobalTheory.ExpDivision.hasTemperateGrowth_div {E g : ℝ → ℂ} (hE : E.HasTemperateGrowth)
    (h0 : ∀ x, E x ≠ 0) {N : ℕ} {M : ℝ} (hM : ∀ x, ‖(E x)⁻¹‖ ≤ M * (1 + ‖x‖) ^ N)
    (hg : g.HasTemperateGrowth) : (fun x => g x / E x).HasTemperateGrowth := by sorry

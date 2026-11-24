-- Prove2me | Theorems.Thm_GlobalTheory_norm_iteratedFDeriv_succ_clm_add_le
-- name    : GlobalTheory.norm_iteratedFDeriv_succ_clm_add_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:55.251559+00:00
-- url     : https://prove2.me/theorems/a173b2eb-b18e-406f-aee1-2c50e6355389
-- title:
--   Global Theory: norm iterated FDeriv succ clm add le
-- statement:
--   The Global Theory construction uses the norm iterated FDeriv succ clm add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivCexpPhaseLe.lean#L20-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivCexpPhaseLe.lean#L20-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivCexpPhaseLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open scoped Nat
noncomputable section
open GlobalTheory

theorem GlobalTheory.norm_iteratedFDeriv_succ_clm_add_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℂ) (h : E → ℂ) (hh : ContDiff ℝ ∞ h) (i : ℕ) (t : E) :
    ‖iteratedFDeriv ℝ (i + 1) (fun t => L t + h t) t‖ ≤ ‖L‖ + ‖iteratedFDeriv ℝ (i + 1) h t‖ := by sorry

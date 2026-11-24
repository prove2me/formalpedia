-- Prove2me | Theorems.Thm_GlobalTheory_norm_iteratedFDeriv_cexp_phase_le
-- name    : GlobalTheory.norm_iteratedFDeriv_cexp_phase_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:02.745703+00:00
-- url     : https://prove2.me/theorems/000c8b41-a85b-4384-8676-86e970b8e103
-- title:
--   Global Theory: norm iterated FDeriv cexp phase le
-- statement:
--   The Global Theory construction uses the norm iterated FDeriv cexp phase le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivCexpPhaseLe.lean#L39-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivCexpPhaseLe.lean#L39-L83

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

theorem GlobalTheory.norm_iteratedFDeriv_cexp_phase_le :
    ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (B : V →L[ℝ] E →L[ℝ] ℂ) (h : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
      (∀ y t, (B y t + h t).re = 0) → ∀ (n : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => Complex.exp (B y t + h t)) t‖ ≤ C * (1 + ‖y‖) ^ n := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_logDerivativeThreeFourOne_term_nonneg
-- name    : GlobalTheory.logDerivativeThreeFourOne.term_nonneg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:08:00.333505+00:00
-- url     : https://prove2.me/theorems/7d44e51d-4b84-4f8a-8944-030805a2a0b6
-- title:
--   log Derivative Three Four One: term nonneg
-- statement:
--   The log Derivative Three Four One construction uses the term nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivativeBound.lean#L25-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivativeBound.lean#L25-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivativeBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.logDerivativeThreeFourOne

theorem GlobalTheory.logDerivativeThreeFourOne.term_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term ((fun n : ℕ => (1 : DirichletCharacter ℂ q) n) *
          (fun n : ℕ => (vonMangoldt n : ℂ))) σ n).re
      + 4 * (LSeries.term ((fun n : ℕ => χ n) * (fun n : ℕ => (vonMangoldt n : ℂ)))
          (σ + t * I) n).re
      + (LSeries.term ((fun n : ℕ => (χ ^ 2) n) * (fun n : ℕ => (vonMangoldt n : ℂ)))
          (σ + 2 * t * I) n).re := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_log_factorial_pow_mul_factorial_pow_le
-- name    : GlobalTheory.log_factorial_pow_mul_factorial_pow_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:08:34.430051+00:00
-- url     : https://prove2.me/theorems/050bb4f8-c13c-4e52-a9bc-ece72ffcf06c
-- title:
--   Global Theory: log factorial pow mul factorial pow le
-- statement:
--   The Global Theory construction uses the log factorial pow mul factorial pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LogFactorialPowMulFactorialPowLe.lean#L5-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LogFactorialPowMulFactorialPowLe.lean#L5-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LogFactorialPowMulFactorialPowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.log_factorial_pow_mul_factorial_pow_le :
    ∀ (n R₀ : ℕ) (R : ℝ), 1 ≤ R → (R₀ : ℝ) ≤ R →
      Real.log (((n.factorial) ^ (2 * R₀) * (R₀.factorial) ^ n : ℕ) : ℝ)
        ≤ 4 * (n : ℝ) * R * Real.log (n * R) := by sorry

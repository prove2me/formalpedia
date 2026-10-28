-- Prove2me | Theorems.Thm_OAI_SKGap_conditional_bad_integral_rate
-- name    : OAI.SKGap.conditional_bad_integral_rate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:21:49.301544+00:00
-- url     : https://prove2.me/theorems/7ddf84de-835d-4666-b21d-0ffc4b00e253
-- title:
--   OAI.SKGap.conditional_bad_integral_rate: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.conditional_bad_integral_rate` of [lean/OAI/Probability/SKGap/Localization/ConditionalIntegralRate.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/ConditionalIntegralRate.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity`, `open scoped BigOperators Matrix.Norms.Frobenius ENNReal`):
--
--   ```lean
--   theorem conditional_bad_integral_rate {j A t0 T : ℝ} (hj : 0 < j) (hj1 : j < 1)
--       (hA : 1 ≤ A) (hsub : sqrt j*A < 1) (ht0 : 0 < t0) (hT : t0 ≤ T) :
--       ∃ m ε σ0 a : ℝ, 0 < m ∧ 0 < ε ∧ 0 < σ0 ∧ 0 < a ∧ ∃ N : ℕ,
--       ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ t ∈ Icc t0 T, ∀ σ ∈ Ioc 0 σ0,
--       (∫⁻ y,reducedBadDensity (n := n) j t σ A ε m y) ≤ ENNReal.ofReal (exp (-a*(n:ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.reducedBadDensity` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.positive_time_root_stability` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/ConditionalIntegralRate.lean (declaration OAI.SKGap.conditional_bad_integral_rate)

import Mathlib
import Definitions.Def_OAIQ072A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

theorem conditional_bad_integral_rate {j A t0 T : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hA : 1 ≤ A) (hsub : sqrt j*A < 1) (ht0 : 0 < t0) (hT : t0 ≤ T) :
    ∃ m ε σ0 a : ℝ, 0 < m ∧ 0 < ε ∧ 0 < σ0 ∧ 0 < a ∧ ∃ N : ℕ,
    ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ t ∈ Icc t0 T, ∀ σ ∈ Ioc 0 σ0,
    (∫⁻ y,reducedBadDensity (n := n) j t σ A ε m y) ≤ ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  sorry
end SKGap
end
end

end OAI
end

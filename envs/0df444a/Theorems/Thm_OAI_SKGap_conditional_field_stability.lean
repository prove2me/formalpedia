-- Prove2me | Theorems.Thm_OAI_SKGap_conditional_field_stability
-- name    : OAI.SKGap.conditional_field_stability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:22:09.751409+00:00
-- url     : https://prove2.me/theorems/4e6c61a8-1f84-41dd-bdc9-524313a12a5e
-- title:
--   OAI.SKGap.conditional_field_stability: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.conditional_field_stability` of [lean/OAI/Probability/SKGap/Stability/ConditionalStability.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/ConditionalStability.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real Set MeasureTheory ProbabilityTheory`, `open scoped BigOperators Matrix.Norms.Frobenius ENNReal`):
--
--   ```lean
--   theorem conditional_field_stability {j A R t0 T : ℝ}
--       (hj : 0 < j) (hj1 : j < 1) (hA : 1 ≤ A) (hsub : sqrt j*A < 1)
--       (hR : 0 ≤ R) (ht0 : 0 < t0) :
--       ∃ m ν σ0 : ℝ, 0 < m ∧ 0 < ν ∧ 0 < σ0 ∧
--       ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧ scalarEqualitySet j R t0 T ⊆ U ∧
--       ∀ R1 : ℝ, 1 ≤ R1 → ∃ ε c : ℝ, ∃ N : ℕ, 0 < ε ∧ 0 < c ∧ 0 < N ∧
--       ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ x ∈ U, ∀ y : Fin n → ℝ,
--       empiricalLaw y=(x.1 : ProbabilityMeasure ℝ) →
--       (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ) →
--       ∀ σ : ℝ, |σ| ≤ σ0 →
--       (conditionalGoeLaw (j/(n:ℝ)) ((x.2:ℝ)+σ^2) (magnetization y)
--         (empiricalObservation j x.2 σ y)).real
--         {W | ((fun i k=>W (i,k)),y) ∈ badFieldSet n j A ε m} ≤ exp (-c*(n:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.ScalarTimeDomain`, `OAI.SKGap.badFieldSet`, `OAI.SKGap.conditionalGoeLaw`, `OAI.SKGap.empiricalLaw`, `OAI.SKGap.empiricalObservation`, `OAI.SKGap.magnetization`, `OAI.SKGap.momentBall` and `OAI.SKGap.scalarEqualitySet` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.conditional_bad_integral_rate` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/ConditionalStability.lean (declaration OAI.SKGap.conditional_field_stability)

import Mathlib
import Definitions.Def_OAIQ072A000

section

attribute [-instance] _root_.OAI.SKGap.conditionalGoeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

theorem conditional_field_stability {j A R t0 T : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hA : 1 ≤ A) (hsub : sqrt j*A < 1)
    (hR : 0 ≤ R) (ht0 : 0 < t0) :
    ∃ m ν σ0 : ℝ, 0 < m ∧ 0 < ν ∧ 0 < σ0 ∧
    ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧ scalarEqualitySet j R t0 T ⊆ U ∧
    ∀ R1 : ℝ, 1 ≤ R1 → ∃ ε c : ℝ, ∃ N : ℕ, 0 < ε ∧ 0 < c ∧ 0 < N ∧
    ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ x ∈ U, ∀ y : Fin n → ℝ,
    empiricalLaw y=(x.1 : ProbabilityMeasure ℝ) →
    (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ) →
    ∀ σ : ℝ, |σ| ≤ σ0 →
    (conditionalGoeLaw (j/(n:ℝ)) ((x.2:ℝ)+σ^2) (magnetization y)
      (empiricalObservation j x.2 σ y)).real
      {W | ((fun i k=>W (i,k)),y) ∈ badFieldSet n j A ε m} ≤ exp (-c*(n:ℝ)) := by
  sorry
end SKGap
end
end

end OAI
end

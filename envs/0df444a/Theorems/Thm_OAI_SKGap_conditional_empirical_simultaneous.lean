-- Prove2me | Theorems.Thm_OAI_SKGap_conditional_empirical_simultaneous
-- name    : OAI.SKGap.conditional_empirical_simultaneous
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:23:50.627568+00:00
-- url     : https://prove2.me/theorems/1807d336-fba0-42e8-9571-3f6cc6b7a493
-- title:
--   OAI.SKGap.conditional_empirical_simultaneous: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.conditional_empirical_simultaneous` of [lean/OAI/Probability/SKGap/Localization/ConditionalWellDefined.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/ConditionalWellDefined.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real Set MeasureTheory ProbabilityTheory`, `open scoped BigOperators Matrix.Norms.Frobenius`):
--
--   ```lean
--   theorem conditional_empirical_simultaneous {j A R t0 T : ℝ}
--       (hj : 0 < j) (hj1 : j < 1) (hA : 1 ≤ A) (hsub : sqrt j*A < 1)
--       (hR : 0 ≤ R) (ht0 : 0 < t0) :
--       ∃ m ν σ0 : ℝ, 0 < m ∧ 0 < ν ∧ 0 < σ0 ∧
--       ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧ scalarEqualitySet j R t0 T ⊆ U ∧
--       ∀ R1 : ℝ, 1 ≤ R1 → ∃ ε c : ℝ, ∃ N : ℕ, 0 < ε ∧ 0 < c ∧ 0 < N ∧
--       ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ x ∈ U, ∀ y : Fin n → ℝ,
--       empiricalLaw y=(x.1 : ProbabilityMeasure ℝ) →
--       (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ) →
--       ∀ σ : ℝ, |σ| ≤ σ0 →
--       (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)).real
--         {g | ∃ a, (∀ i,a i ∈ Icc 0 A) ∧
--           (∑ i,(a i-(1-tanh (y i)^2))^2) ≤ ε^2*(n:ℝ) ∧
--           ¬(diagonalHessian a (empiricalConditionalMiddle j x.2 σ y g)-
--             m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef} ≤
--         103*exp (-c*(n:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.ScalarTimeDomain`, `OAI.SKGap.diagonalHessian`, `OAI.SKGap.empiricalConditionalMiddle`, `OAI.SKGap.empiricalLaw`, `OAI.SKGap.momentBall` and `OAI.SKGap.scalarEqualitySet` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.conditional_field_stability` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/ConditionalWellDefined.lean (declaration OAI.SKGap.conditional_empirical_simultaneous)

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
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

theorem conditional_empirical_simultaneous {j A R t0 T : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hA : 1 ≤ A) (hsub : sqrt j*A < 1)
    (hR : 0 ≤ R) (ht0 : 0 < t0) :
    ∃ m ν σ0 : ℝ, 0 < m ∧ 0 < ν ∧ 0 < σ0 ∧
    ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧ scalarEqualitySet j R t0 T ⊆ U ∧
    ∀ R1 : ℝ, 1 ≤ R1 → ∃ ε c : ℝ, ∃ N : ℕ, 0 < ε ∧ 0 < c ∧ 0 < N ∧
    ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ x ∈ U, ∀ y : Fin n → ℝ,
    empiricalLaw y=(x.1 : ProbabilityMeasure ℝ) →
    (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ) →
    ∀ σ : ℝ, |σ| ≤ σ0 →
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)).real
      {g | ∃ a, (∀ i,a i ∈ Icc 0 A) ∧
        (∑ i,(a i-(1-tanh (y i)^2))^2) ≤ ε^2*(n:ℝ) ∧
        ¬(diagonalHessian a (empiricalConditionalMiddle j x.2 σ y g)-
          m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef} ≤
      103*exp (-c*(n:ℝ)) := by
  sorry
end SKGap
end
end

end OAI
end

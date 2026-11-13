-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorContactObjective_exists_minimum
-- name    : OAI.InvariantIsing.tensorContactObjective_exists_minimum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:44:46.2062+00:00
-- url     : https://prove2.me/theorems/56e95b8e-b95d-483d-b236-6127b2543916
-- title:
--   OAI.InvariantIsing.tensorContactObjective_exists_minimum: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorContactObjective_exists_minimum` of [lean/OAI/Probability/InvariantIsing/Arrays/TensorContactMinimum.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorContactMinimum.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set`, `open scoped BigOperators`):
--
--   ```lean
--   theorem tensorContactObjective_exists_minimum (hhaar : HaarConcentrationInput)
--       (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
--       (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
--       (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (hb : CascadeExponents n b)
--       (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (w : Fin (n + 1) → ℝ)
--       (S : ℝ) (V : ℝ → ℝ) (hV : Continuous V) (H : ℝ) (hH : 0 ≤ H) :
--       ∃ p ∈ tensorContactRegion N m n H,
--         ∀ q ∈ tensorContactRegion N m n H,
--           tensorContactObjective μ eig c I b w S V p ≤ tensorContactObjective μ eig c I b w S V q
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput`, `OAI.InvariantIsing.SpecialOrthogonal` and `OAI.InvariantIsing.TensorContactParameter` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.HaarConcentrationInput` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorContactRegion` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.tensorContactObjective` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proof of `OAI.InvariantIsing.finiteSpectrum_meanPressure_variational_upper` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorContactMinimum.lean (declaration OAI.InvariantIsing.tensorContactObjective_exists_minimum)

import Mathlib
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

theorem tensorContactObjective_exists_minimum (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (w : Fin (n + 1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (hV : Continuous V) (H : ℝ) (hH : 0 ≤ H) :
    ∃ p ∈ tensorContactRegion N m n H,
      ∀ q ∈ tensorContactRegion N m n H,
        tensorContactObjective μ eig c I b w S V p ≤ tensorContactObjective μ eig c I b w S V q := by
  sorry

end InvariantIsing

end

end OAI
end

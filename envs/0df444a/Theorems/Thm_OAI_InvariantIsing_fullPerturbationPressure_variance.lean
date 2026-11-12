-- Prove2me | Theorems.Thm_OAI_InvariantIsing_fullPerturbationPressure_variance
-- name    : OAI.InvariantIsing.fullPerturbationPressure_variance
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:38:41.91363+00:00
-- url     : https://prove2.me/theorems/f16d391a-157d-4cc8-b2ef-1e7294b2d047
-- title:
--   OAI.InvariantIsing.fullPerturbationPressure_variance: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.fullPerturbationPressure_variance` of [lean/OAI/Probability/InvariantIsing/Arrays/FullPerturbationVariance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/FullPerturbationVariance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators NNReal`):
--
--   ```lean
--   theorem fullPerturbationPressure_variance (hhaar : HaarConcentrationInput)
--       (hgauss : GaussianLipschitzVarianceInput) :
--       ∃ C : ℝ, 0 < C ∧
--       ∀ N : ℕ, 3 ≤ N →
--       ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
--       ∀ m : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
--       ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, |u j| ≤ 2) →
--       ∀ v : Fin m → ℝ, (∀ a, |v a| ≤ 2) → ∀ t : ℝ, |t| ≤ 1 →
--       ∀ n : ℕ, ∀ b : ℕ → ℝ, CascadeExponents n b →
--       ∀ h : ℕ → ℝ, Monotone h → 0 ≤ h 0 → ∀ H : ℝ, h n ≤ H →
--         let degree := fun j : Fin N => enumeratedSpectralDegree m j
--         let treeDegree := fun j : Fin N => enumeratedTreeDegree m j
--         let profile := tensorPathProfile I degree n treeDegree h
--         let P := tensorRootTreeLaw I degree n b (fun i => profile (i + 1)) (profile 0)
--         let F := tensorDisorderPressure (diagonalPerturbedEigenvalues eig I v t) c I degree
--           (tensorPerturbationAmplitude N u) n
--         MemLp F 2 (μ.prod P) ∧ variance F (μ.prod P) ≤
--           (4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
--             ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 +
--               C * (K + 4 * m + 8) ^ 2) / N
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` and `OAI.InvariantIsing.SpinTensorIndex` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput`, `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.diagonalPerturbedEigenvalues`, `OAI.InvariantIsing.enumeratedSpectralDegree`, `OAI.InvariantIsing.enumeratedTreeDegree` and `OAI.InvariantIsing.tensorPerturbationAmplitude` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.HaarConcentrationInput` and `OAI.InvariantIsing.tensorPathProfile` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorRootTreeLaw` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.tensorDisorderPressure` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.RawTree`, `OAI.IsingPerceptron.noiseTreeMeasurableSpace`, `OAI.IsingPerceptron.rawCascadeLaw`, `OAI.IsingPerceptron.rawTreeMeasurableSpace` and `OAI.IsingPerceptron.rawTreeTotal` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_fixed_minimum_geometric_limit` and `OAI.InvariantIsing.tensorPerturbation_minimizers_have_GG_limit` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/FullPerturbationVariance.lean (declaration OAI.InvariantIsing.fullPerturbationPressure_variance)

import Mathlib
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

theorem fullPerturbationPressure_variance (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, |u j| ≤ 2) →
    ∀ v : Fin m → ℝ, (∀ a, |v a| ≤ 2) → ∀ t : ℝ, |t| ≤ 1 →
    ∀ n : ℕ, ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ h : ℕ → ℝ, Monotone h → 0 ≤ h 0 → ∀ H : ℝ, h n ≤ H →
      let degree := fun j : Fin N => enumeratedSpectralDegree m j
      let treeDegree := fun j : Fin N => enumeratedTreeDegree m j
      let profile := tensorPathProfile I degree n treeDegree h
      let P := tensorRootTreeLaw I degree n b (fun i => profile (i + 1)) (profile 0)
      let F := tensorDisorderPressure (diagonalPerturbedEigenvalues eig I v t) c I degree
        (tensorPerturbationAmplitude N u) n
      MemLp F 2 (μ.prod P) ∧ variance F (μ.prod P) ≤
        (4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
          ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 +
            C * (K + 4 * m + 8) ^ 2) / N := by
  sorry

end InvariantIsing

end

end OAI
end

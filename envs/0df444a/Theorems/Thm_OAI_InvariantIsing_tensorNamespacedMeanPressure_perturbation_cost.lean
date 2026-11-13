-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorNamespacedMeanPressure_perturbation_cost
-- name    : OAI.InvariantIsing.tensorNamespacedMeanPressure_perturbation_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:45:56.59387+00:00
-- url     : https://prove2.me/theorems/52820389-3caa-4422-bb8a-7dab86565fbb
-- title:
--   OAI.InvariantIsing.tensorNamespacedMeanPressure_perturbation_cost: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorNamespacedMeanPressure_perturbation_cost` of [lean/OAI/Probability/InvariantIsing/Arrays/TensorPerturbationBaseComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorPerturbationBaseComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators`):
--
--   ```lean
--   theorem tensorNamespacedMeanPressure_perturbation_cost
--       (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
--       {N m : ℕ} (hN : 3 ≤ N) (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
--       (hμ : μ.IsMulLeftInvariant) (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
--       (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
--       (t : ℝ) (n : ℕ) (b h : ℕ → ℝ) (hb : CascadeExponents n b)
--       (hh : Monotone h) (h0 : 0 ≤ h 0) :
--       |tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v t) c I
--           (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
--           n b (fun j => enumeratedTreeDegree m j) h -
--         ((∫ U : SpecialOrthogonal N,
--           tensorEnrichedPressure (fun i => t * eig i) (specialRotation U) c I
--             (fun j : Fin N => enumeratedSpectralDegree m j) 0 n b
--             (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
--               n (fun j => enumeratedTreeDegree m j) h (i + 1))
--             (tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
--               n (fun j => enumeratedTreeDegree m j) h 0) ∂μ) - h n / 2)| ≤
--         2 * m * perturbationScale N + 8 * perturbationScale N ^ 2
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput`, `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.diagonalPerturbedEigenvalues`, `OAI.InvariantIsing.enumeratedSpectralDegree`, `OAI.InvariantIsing.enumeratedTreeDegree`, `OAI.InvariantIsing.specialRotation` and `OAI.InvariantIsing.tensorPerturbationAmplitude` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.HaarConcentrationInput` and `OAI.InvariantIsing.tensorPathProfile` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorEnrichedPressure` and `OAI.InvariantIsing.tensorNamespacedMeanPressure` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents` and `OAI.IsingPerceptron.perturbationScale` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.finiteSpectrum_meanPressure_variational_upper` and `OAI.InvariantIsing.tensor_envelope_pressure_lower` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorPerturbationBaseComparison.lean (declaration OAI.InvariantIsing.tensorNamespacedMeanPressure_perturbation_cost)

import Mathlib
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem tensorNamespacedMeanPressure_perturbation_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m : ℕ} (hN : 3 ≤ N) (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (hμ : μ.IsMulLeftInvariant) (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (t : ℝ) (n : ℕ) (b h : ℕ → ℝ) (hb : CascadeExponents n b)
    (hh : Monotone h) (h0 : 0 ≤ h 0) :
    |tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v t) c I
        (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
        n b (fun j => enumeratedTreeDegree m j) h -
      ((∫ U : SpecialOrthogonal N,
        tensorEnrichedPressure (fun i => t * eig i) (specialRotation U) c I
          (fun j : Fin N => enumeratedSpectralDegree m j) 0 n b
          (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
            n (fun j => enumeratedTreeDegree m j) h (i + 1))
          (tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
            n (fun j => enumeratedTreeDegree m j) h 0) ∂μ) - h n / 2)| ≤
      2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 := by
  sorry

end InvariantIsing

end

end OAI
end

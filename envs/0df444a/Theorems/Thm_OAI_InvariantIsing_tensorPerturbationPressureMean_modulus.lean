-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorPerturbationPressureMean_modulus
-- name    : OAI.InvariantIsing.tensorPerturbationPressureMean_modulus
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:45:51.576196+00:00
-- url     : https://prove2.me/theorems/57562a64-6688-4284-8b2e-fe8898801d9c
-- title:
--   OAI.InvariantIsing.tensorPerturbationPressureMean_modulus: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorPerturbationPressureMean_modulus` of [lean/OAI/Probability/InvariantIsing/Arrays/TensorObjectiveContinuity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorObjectiveContinuity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set`, `open scoped BigOperators Topology NNReal ENNReal`):
--
--   ```lean
--   lemma tensorPerturbationPressureMean_modulus (hhaar : HaarConcentrationInput)
--       (hgauss : GaussianLipschitzVarianceInput) {N m : ℕ} (hN : 3 ≤ N)
--       (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
--       (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
--       (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
--       (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
--       (u u' : Fin N → ℝ) (v v' : Fin m → ℝ) :
--       |tensorPerturbationPressureMean μ eig c I u v t n b h -
--         tensorPerturbationPressureMean μ eig c I u' v' t n b h| ≤
--         2 * (N : ℝ)⁻¹ * tensorAmplitudeModulus
--           (tensorPerturbationAmplitude N u) (tensorPerturbationAmplitude N u') +
--           perturbationScale N * ∑ a, |v a - v' a|
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput`, `OAI.InvariantIsing.SpecialOrthogonal` and `OAI.InvariantIsing.tensorPerturbationAmplitude` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.tensorAmplitudeModulus` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.HaarConcentrationInput` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorPerturbationPressureMean` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents` and `OAI.IsingPerceptron.perturbationScale` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.tensorContactObjective_exists_minimum` and `OAI.InvariantIsing.tensor_zero_field_minimizing_sequence` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorObjectiveContinuity.lean (declaration OAI.InvariantIsing.tensorPerturbationPressureMean_modulus)

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

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology NNReal ENNReal

namespace InvariantIsing

lemma tensorPerturbationPressureMean_modulus (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u u' : Fin N → ℝ) (v v' : Fin m → ℝ) :
    |tensorPerturbationPressureMean μ eig c I u v t n b h -
      tensorPerturbationPressureMean μ eig c I u' v' t n b h| ≤
      2 * (N : ℝ)⁻¹ * tensorAmplitudeModulus
        (tensorPerturbationAmplitude N u) (tensorPerturbationAmplitude N u') +
        perturbationScale N * ∑ a, |v a - v' a| := by
  sorry

end InvariantIsing

end

end OAI
end

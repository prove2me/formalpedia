-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorNamespacedMeanPressure_field_modulus
-- name    : OAI.InvariantIsing.tensorNamespacedMeanPressure_field_modulus
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:45:42.171221+00:00
-- url     : https://prove2.me/theorems/5748acec-be2e-4765-84b2-6d3666d52e36
-- title:
--   OAI.InvariantIsing.tensorNamespacedMeanPressure_field_modulus: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorNamespacedMeanPressure_field_modulus` of [lean/OAI/Probability/InvariantIsing/Arrays/TensorFieldModulus.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorFieldModulus.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set`, `open scoped BigOperators`):
--
--   ```lean
--   theorem tensorNamespacedMeanPressure_field_modulus {N m k : ℕ} (hN : 0 < N)
--       (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
--       (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
--       (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (a c' : Fin (n + 1) → ℝ)
--       (ha : ∀ j, 0 ≤ a j) (hc : ∀ j, 0 ≤ c' j) :
--       |tensorNamespacedMeanPressure μ eig c I degree amp n b r (finiteFieldPath a) -
--         tensorNamespacedMeanPressure μ eig c I degree amp n b r (finiteFieldPath c')| ≤
--         (∑ j, |a j - c' j|) / 2
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal` (definitions bundle `OAIQ258001` of this split); `OAI.IsingPerceptron.finiteFieldPath` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.tensorNamespacedMeanPressure` (definitions bundle `OAIQ258005` of this split).
--
--   **Used by.** The proof of `OAI.InvariantIsing.tensorContactObjective_exists_minimum` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorFieldModulus.lean (declaration OAI.InvariantIsing.tensorNamespacedMeanPressure_field_modulus)

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

theorem tensorNamespacedMeanPressure_field_modulus {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (a c' : Fin (n + 1) → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hc : ∀ j, 0 ≤ c' j) :
    |tensorNamespacedMeanPressure μ eig c I degree amp n b r (finiteFieldPath a) -
      tensorNamespacedMeanPressure μ eig c I degree amp n b r (finiteFieldPath c')| ≤
      (∑ j, |a j - c' j|) / 2 := by
  sorry

end InvariantIsing

end

end OAI
end

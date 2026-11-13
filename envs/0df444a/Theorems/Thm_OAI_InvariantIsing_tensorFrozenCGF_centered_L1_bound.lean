-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorFrozenCGF_centered_L1_bound
-- name    : OAI.InvariantIsing.tensorFrozenCGF_centered_L1_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:45:01.980401+00:00
-- url     : https://prove2.me/theorems/0fc52db2-3bf9-4ba8-bb7a-11c19b2f04fc
-- title:
--   OAI.InvariantIsing.tensorFrozenCGF_centered_L1_bound: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorFrozenCGF_centered_L1_bound` of [lean/OAI/Probability/InvariantIsing/Arrays/NSpinTensorFrozenFluctuation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/NSpinTensorFrozenFluctuation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators NNReal ENNReal`):
--
--   ```lean
--   theorem tensorFrozenCGF_centered_L1_bound {N m k : ℕ} (hN : 0 < N)
--       (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
--       (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
--       (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
--       (hh : Monotone h) (h0 : 0 ≤ h 0) (hb : CascadeExponents n b) (j : Fin k) (t B : ℝ)
--       (hF : ∀ a : ℝ, a = t ∨ a = 0 →
--         MemLp (tensorDisorderPressure eig c I degree (Function.update amplitude j a) n) 2
--           (μ.prod (tensorRootTreeLaw I degree n b
--             (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
--             (tensorPathProfile I degree n treeDegree h 0))))
--       (hv : ∀ a : ℝ, a = t ∨ a = 0 →
--         variance (tensorDisorderPressure eig c I degree (Function.update amplitude j a) n)
--           (μ.prod (tensorRootTreeLaw I degree n b
--             (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
--             (tensorPathProfile I degree n treeDegree h 0))) ≤ B) :
--       let Q := (tensorFrozenLaw μ n b j).prod gaussianCoordinates
--       let Z := tensorFrozenCGF eig c I degree amplitude n treeDegree h j t
--       MemLp Z 2 Q ∧ (∫ p, |Z p - ∫ p', Z p' ∂Q| ∂Q) ≤ 2 * N * Real.sqrt B
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` and `OAI.InvariantIsing.SpinTensorIndex` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal` and `OAI.InvariantIsing.TensorFrozenData` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.tensorPathProfile` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorFrozenLaw` and `OAI.InvariantIsing.tensorRootTreeLaw` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.tensorDisorderPressure` and `OAI.InvariantIsing.tensorFrozenCGF` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.OtherNamespaces`, `OAI.IsingPerceptron.gaussianCoordinates`, `OAI.IsingPerceptron.labeledTreeMeasurableSpace` and `OAI.IsingPerceptron.noiseTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_fixed_minimum_geometric_limit` and `OAI.InvariantIsing.tensorPerturbation_minimizers_have_GG_limit` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/NSpinTensorFrozenFluctuation.lean (declaration OAI.InvariantIsing.tensorFrozenCGF_centered_L1_bound)

import Mathlib
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal ENNReal

namespace InvariantIsing

theorem tensorFrozenCGF_centered_L1_bound {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hb : CascadeExponents n b) (j : Fin k) (t B : ℝ)
    (hF : ∀ a : ℝ, a = t ∨ a = 0 →
      MemLp (tensorDisorderPressure eig c I degree (Function.update amplitude j a) n) 2
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
          (tensorPathProfile I degree n treeDegree h 0))))
    (hv : ∀ a : ℝ, a = t ∨ a = 0 →
      variance (tensorDisorderPressure eig c I degree (Function.update amplitude j a) n)
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
          (tensorPathProfile I degree n treeDegree h 0))) ≤ B) :
    let Q := (tensorFrozenLaw μ n b j).prod gaussianCoordinates
    let Z := tensorFrozenCGF eig c I degree amplitude n treeDegree h j t
    MemLp Z 2 Q ∧ (∫ p, |Z p - ∫ p', Z p' ∂Q| ∂Q) ≤ 2 * N * Real.sqrt B := by
  sorry

end InvariantIsing

end

end OAI
end

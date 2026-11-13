-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorDiagonal_fluctuation_at_minimum
-- name    : OAI.InvariantIsing.tensorDiagonal_fluctuation_at_minimum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:44:41.924706+00:00
-- url     : https://prove2.me/theorems/86453d68-75e9-44e7-a5f2-07f3090d38e3
-- title:
--   OAI.InvariantIsing.tensorDiagonal_fluctuation_at_minimum: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorDiagonal_fluctuation_at_minimum` of [lean/OAI/Probability/InvariantIsing/Arrays/TensorMinimumFluctuations.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorMinimumFluctuations.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators`):
--
--   ```lean
--   theorem tensorDiagonal_fluctuation_at_minimum {N m k : ℕ} (hN : 0 < N)
--       (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
--       (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
--       (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
--       (hh : Monotone h) (h0 : 0 ≤ h 0) (hb : CascadeExponents n b)
--       (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w L : ℝ)
--       (hw : w ∈ Set.Icc (1 : ℝ) 2) (he : perturbationScale N ≤ 1 / 32)
--       (hs : contactStep N ≤ 1 / 4)
--       (hF : ∀ q : ℝ, |q| ≤ 2 →
--         MemLp (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
--           c I degree amplitude n) 2 (μ.prod (tensorRootTreeLaw I degree n b
--             (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))))
--       (hv : ∀ q : ℝ, |q| ≤ 2 →
--         variance (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
--           c I degree amplitude n) (μ.prod (tensorRootTreeLaw I degree n b
--             (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) ≤ L / N)
--       (hmin :
--         let R := μ.prod (tensorRootTreeLaw I degree n b
--           (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))
--         let M := fun q => ∫ p, tensorDisorderPressure
--           (diagonalPerturbedEigenvalues eig I (Function.update v a q) t) c I degree amplitude n p ∂ R
--         ∀ q ∈ Set.Icc (1 : ℝ) 2, -M w + (w - 3 / 2) ^ 2 ≤ -M q + (q - 3 / 2) ^ 2) :
--       let A := N * perturbationScale N
--       let center := 2 * (N / A ^ 2) * (A * w - A * (3 / 2))
--       tensorNamespacedObservableAverage μ
--         (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude n b r h
--         (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center|) ≤
--         diagonalContactRate N L
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` and `OAI.InvariantIsing.SpinTensorIndex` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.diagonalPerturbedEigenvalues` and `OAI.InvariantIsing.specialRotation` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.diagonalContactRate` and `OAI.IsingPerceptron.contactStep` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.projectedOverlap` and `OAI.InvariantIsing.tensorPathProfile` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorRootTreeLaw` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.tensorDisorderPressure` and `OAI.InvariantIsing.tensorNamespacedObservableAverage` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.noiseTreeMeasurableSpace` and `OAI.IsingPerceptron.perturbationScale` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_fixed_minimum_geometric_limit` and `OAI.InvariantIsing.tensorPerturbation_minimizers_have_GG_limit` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorMinimumFluctuations.lean (declaration OAI.InvariantIsing.tensorDiagonal_fluctuation_at_minimum)

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem tensorDiagonal_fluctuation_at_minimum {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hb : CascadeExponents n b)
    (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w L : ℝ)
    (hw : w ∈ Set.Icc (1 : ℝ) 2) (he : perturbationScale N ≤ 1 / 32)
    (hs : contactStep N ≤ 1 / 4)
    (hF : ∀ q : ℝ, |q| ≤ 2 →
      MemLp (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude n) 2 (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))))
    (hv : ∀ q : ℝ, |q| ≤ 2 →
      variance (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude n) (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) ≤ L / N)
    (hmin :
      let R := μ.prod (tensorRootTreeLaw I degree n b
        (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))
      let M := fun q => ∫ p, tensorDisorderPressure
        (diagonalPerturbedEigenvalues eig I (Function.update v a q) t) c I degree amplitude n p ∂ R
      ∀ q ∈ Set.Icc (1 : ℝ) 2, -M w + (w - 3 / 2) ^ 2 ≤ -M q + (q - 3 / 2) ^ 2) :
    let A := N * perturbationScale N
    let center := 2 * (N / A ^ 2) * (A * w - A * (3 / 2))
    tensorNamespacedObservableAverage μ
      (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude n b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center|) ≤
      diagonalContactRate N L := by
  sorry

end InvariantIsing

end

end OAI
end

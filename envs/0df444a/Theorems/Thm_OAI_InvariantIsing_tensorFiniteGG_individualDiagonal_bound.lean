-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorFiniteGG_individualDiagonal_bound
-- name    : OAI.InvariantIsing.tensorFiniteGG_individualDiagonal_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:45:09.635562+00:00
-- url     : https://prove2.me/theorems/1dfc403f-2ef1-4ad1-9975-1180bfa4c0ff
-- title:
--   OAI.InvariantIsing.tensorFiniteGG_individualDiagonal_bound: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorFiniteGG_individualDiagonal_bound` of [lean/OAI/Probability/InvariantIsing/Arrays/TensorFiniteGG.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorFiniteGG.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators`):
--
--   ```lean
--   theorem tensorFiniteGG_individualDiagonal_bound {N m k q : ℕ}
--       (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
--       (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
--       (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
--       (j : Fin k) (β e C : ℝ) (hC : 0 ≤ C) (ha : 0 < |amplitude j|)
--       (D : SpecialOrthogonal N → (Fin (q + 1) → Spin N × LabeledLeaf n) → ℝ)
--       (hD : Measurable (Function.uncurry D)) (hDb : ∀ U σ, |D U σ| ≤ C)
--       (center δ : Fin m → ℝ)
--       (hδ : ∀ a, tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
--         (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center a|) ≤ δ a)
--       (hE :
--         let A := spectralPerturbationCoefficients (fun ω : TensorFrozenData N n j => ω.1.1)
--           I (degree j) n (r j)
--         let ν := tensorFrozenReference eig c I degree amplitude n r h j
--         let E := fun p : TensorFrozenData N n j × (ℕ → ℝ) => ∫ x,
--           |cylinderField (A p.1 x) p.2 - β|
--           ∂(ν p.1).tilted (fun x => amplitude j * cylinderField (A p.1 x) p.2)
--         Integrable E ((tensorFrozenLaw μ n b j).prod gaussianCoordinates) ∧
--           (∫ p, E p ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates) ≤ e) :
--       |tensorSpectralGGResidual μ eig c I degree amplitude n b r h j D| ≤
--         2 * C * (e / |amplitude j| + ∑ a, (degree j a : ℝ) * δ a)
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.TensorFrozenData` and `OAI.InvariantIsing.specialRotation` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.projectedOverlap` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorFrozenLaw` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.spectralPerturbationCoefficients`, `OAI.InvariantIsing.tensorFrozenReference`, `OAI.InvariantIsing.tensorNamespacedObservableAverage` and `OAI.InvariantIsing.tensorSpectralGGResidual` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.OtherNamespaces`, `OAI.IsingPerceptron.cylinderField`, `OAI.IsingPerceptron.gaussianCoordinates`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace` and `OAI.IsingPerceptron.labeledTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_fixed_minimum_geometric_limit` and `OAI.InvariantIsing.tensorPerturbation_minimizers_have_GG_limit` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorFiniteGG.lean (declaration OAI.InvariantIsing.tensorFiniteGG_individualDiagonal_bound)

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem tensorFiniteGG_individualDiagonal_bound {N m k q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (β e C : ℝ) (hC : 0 ≤ C) (ha : 0 < |amplitude j|)
    (D : SpecialOrthogonal N → (Fin (q + 1) → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) (hDb : ∀ U σ, |D U σ| ≤ C)
    (center δ : Fin m → ℝ)
    (hδ : ∀ a, tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center a|) ≤ δ a)
    (hE :
      let A := spectralPerturbationCoefficients (fun ω : TensorFrozenData N n j => ω.1.1)
        I (degree j) n (r j)
      let ν := tensorFrozenReference eig c I degree amplitude n r h j
      let E := fun p : TensorFrozenData N n j × (ℕ → ℝ) => ∫ x,
        |cylinderField (A p.1 x) p.2 - β|
        ∂(ν p.1).tilted (fun x => amplitude j * cylinderField (A p.1 x) p.2)
      Integrable E ((tensorFrozenLaw μ n b j).prod gaussianCoordinates) ∧
        (∫ p, E p ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates) ≤ e) :
    |tensorSpectralGGResidual μ eig c I degree amplitude n b r h j D| ≤
      2 * C * (e / |amplitude j| + ∑ a, (degree j a : ℝ) * δ a) := by
  sorry

end InvariantIsing

end

end OAI
end

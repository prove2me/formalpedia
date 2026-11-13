-- Prove2me | Theorems.Thm_OAI_InvariantIsing_priorNamespacedArrayLaw_diagonalWard_bound
-- name    : OAI.InvariantIsing.priorNamespacedArrayLaw_diagonalWard_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:40:37.330226+00:00
-- url     : https://prove2.me/theorems/1993ee46-efcb-45a9-b2fe-1882fdd15abd
-- title:
--   OAI.InvariantIsing.priorNamespacedArrayLaw_diagonalWard_bound: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.priorNamespacedArrayLaw_diagonalWard_bound` of [lean/OAI/Probability/InvariantIsing/Fields/PriorArrayDiagonalWard.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/PriorArrayDiagonalWard.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators Topology NNReal`):
--
--   ```lean
--   theorem priorNamespacedArrayLaw_diagonalWard_bound {N m n : ℕ} (hN : 0 < N)
--       (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
--       (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
--       (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
--       (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
--       (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
--       (hdegree : ∀ r, (∑ j, (degree r j : ℝ)) ≤ D * ((r : ℝ) + 1))
--       (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
--       (κ : Fin m → ℝ) (a d : Fin m) (had : Disjoint (I a) (I d))
--       (ha : ∀ i ∈ I a, eig i = κ a) (hd : ∀ i ∈ I d, eig i = κ d) :
--       |spectralDiagonalWardResidual
--         (priorNamespacedArrayLaw μ ν eig c I degree (tensorPerturbationAmplitude N u) treeDegree h)
--         (fun j => ((I j).card : ℝ) / N) κ a d| ≤ 48 * D * perturbationScale N ^ 2
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal` and `OAI.InvariantIsing.tensorPerturbationAmplitude` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.spectralDiagonalWardResidual` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.priorNamespacedArrayLaw` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace` and `OAI.IsingPerceptron.perturbationScale` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.priorPerturbedArrayLaw_ward_limits` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/PriorArrayDiagonalWard.lean (declaration OAI.InvariantIsing.priorNamespacedArrayLaw_diagonalWard_bound)

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology NNReal
namespace InvariantIsing

theorem priorNamespacedArrayLaw_diagonalWard_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ j, (degree r j : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (κ : Fin m → ℝ) (a d : Fin m) (had : Disjoint (I a) (I d))
    (ha : ∀ i ∈ I a, eig i = κ a) (hd : ∀ i ∈ I d, eig i = κ d) :
    |spectralDiagonalWardResidual
      (priorNamespacedArrayLaw μ ν eig c I degree (tensorPerturbationAmplitude N u) treeDegree h)
      (fun j => ((I j).card : ℝ) / N) κ a d| ≤ 48 * D * perturbationScale N ^ 2 := by
  sorry

end InvariantIsing

end

end OAI
end

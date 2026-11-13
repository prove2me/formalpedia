-- Prove2me | Theorems.Thm_OAI_InvariantIsing_spinPriorContact_minimum_field_cone
-- name    : OAI.InvariantIsing.spinPriorContact_minimum_field_cone
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:43:53.443195+00:00
-- url     : https://prove2.me/theorems/b7ef2b6e-9946-4aa1-8f91-79cb37530971
-- title:
--   OAI.InvariantIsing.spinPriorContact_minimum_field_cone: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.spinPriorContact_minimum_field_cone` of [lean/OAI/Probability/InvariantIsing/Fields/SpinPriorContactField.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/SpinPriorContactField.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem spinPriorContact_minimum_field_cone {N m n : ℕ} (hN : 0 < N)
--       (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
--       (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
--       (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ)
--       (S : ℝ) (V : ℝ → ℝ) (H : ℝ) (p : TensorContactParameter N m n)
--       (hp : p ∈ tensorContactRegion N m n H)
--       (hmin : ∀ q ∈ tensorContactRegion N m n H,
--         spinPriorContactObjective μ π eig c I b w S V p ≤ spinPriorContactObjective μ π eig c I b w S V q)
--       (hcap : (∑ i, p.2.1 i) < H) (d : Fin (n + 1) → ℝ) (hd : ∀ i, 0 ≤ d i) :
--       (∑ i, w i * finiteFieldPath d i) ≤
--         spinPriorReplicaAverage μ π (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1) c I
--           (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
--           n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
--           (fun _ => tensorFieldPairObservable (finiteFieldPath d))
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.TensorContactParameter`, `OAI.InvariantIsing.diagonalPerturbedEigenvalues`, `OAI.InvariantIsing.enumeratedSpectralDegree`, `OAI.InvariantIsing.enumeratedTreeDegree` and `OAI.InvariantIsing.tensorPerturbationAmplitude` (definitions bundle `OAIQ258001` of this split); `OAI.IsingPerceptron.finiteFieldPath` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.tensorContactRegion` and `OAI.InvariantIsing.tensorFieldPairObservable` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.spinPriorContactObjective` and `OAI.InvariantIsing.spinPriorReplicaAverage` (definitions bundle `OAIQ258005` of this split); `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.spinPriorContact_limit_tail_order` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/SpinPriorContactField.lean (declaration OAI.InvariantIsing.spinPriorContact_minimum_field_cone)

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem spinPriorContact_minimum_field_cone {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (H : ℝ) (p : TensorContactParameter N m n)
    (hp : p ∈ tensorContactRegion N m n H)
    (hmin : ∀ q ∈ tensorContactRegion N m n H,
      spinPriorContactObjective μ π eig c I b w S V p ≤ spinPriorContactObjective μ π eig c I b w S V q)
    (hcap : (∑ i, p.2.1 i) < H) (d : Fin (n + 1) → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (∑ i, w i * finiteFieldPath d i) ≤
      spinPriorReplicaAverage μ π (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1) c I
        (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
        n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
        (fun _ => tensorFieldPairObservable (finiteFieldPath d)) := by
  sorry

end InvariantIsing

end

end OAI
end

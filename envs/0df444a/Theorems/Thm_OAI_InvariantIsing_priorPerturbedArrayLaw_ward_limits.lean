-- Prove2me | Theorems.Thm_OAI_InvariantIsing_priorPerturbedArrayLaw_ward_limits
-- name    : OAI.InvariantIsing.priorPerturbedArrayLaw_ward_limits
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:40:55.623576+00:00
-- url     : https://prove2.me/theorems/6df6764c-ea1d-4e94-a2b9-a24bd2c4946c
-- title:
--   OAI.InvariantIsing.priorPerturbedArrayLaw_ward_limits: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.priorPerturbedArrayLaw_ward_limits` of [lean/OAI/Probability/InvariantIsing/Fields/PriorPerturbedWardLimits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/PriorPerturbedWardLimits.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem priorPerturbedArrayLaw_ward_limits
--       (N : ℕ → ℕ) (hN : ∀ k, 0<N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
--       (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
--       (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
--       (ν : (k : ℕ) → Measure (Spin (N k) × LabeledLeaf n)) [∀ k, IsProbabilityMeasure (ν k)]
--       (eig c : (k : ℕ) → Fin (N k) → ℝ)
--       (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
--       (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
--       (hcover : ∀ k, Finset.univ.biUnion (I k)=Finset.univ)
--       (lam : Fin m → ℝ) (hlam : ∀ k a i, i∈I k a → eig k i=lam a)
--       (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, |u k j|≤2)
--       (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a|≤2)
--       (t : ℕ → ℝ) {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀))
--       (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0≤h k 0)
--       (Q : ProbabilityMeasure (SpectralArray (m+1)))
--       (hL : Tendsto (fun k => priorPerturbedArrayLaw (μ k) (ν k) (eig k) (c k) (I k)
--         (u k) (v k) (t k) (h k)) atTop (𝓝 Q))
--       (ρ : Fin m → ℝ)
--       (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ)) :
--       (∀ a b, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ r, |Φ r|≤B) →
--         spectralOffWardResidual Q ρ (fun a => t₀*lam a) a b Φ=0) ∧
--       (∀ a b, spectralDiagonalWardResidual Q ρ (fun a => t₀*lam a) a b=0)
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.SpectralArray` and `OAI.InvariantIsing.SpectralEntry` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.spectralDiagonalWardResidual` and `OAI.InvariantIsing.spectralOffWardResidual` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.priorPerturbedArrayLaw` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.LabeledLeaf` and `OAI.IsingPerceptron.labeledLeafMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.offset_window_minimum_trial_witness` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/PriorPerturbedWardLimits.lean (declaration OAI.InvariantIsing.priorPerturbedArrayLaw_ward_limits)

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem priorPerturbedArrayLaw_ward_limits
    (N : ℕ → ℕ) (hN : ∀ k, 0<N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (ν : (k : ℕ) → Measure (Spin (N k) × LabeledLeaf n)) [∀ k, IsProbabilityMeasure (ν k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k)=Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i∈I k a → eig k i=lam a)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, |u k j|≤2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a|≤2)
    (t : ℕ → ℝ) {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀))
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0≤h k 0)
    (Q : ProbabilityMeasure (SpectralArray (m+1)))
    (hL : Tendsto (fun k => priorPerturbedArrayLaw (μ k) (ν k) (eig k) (c k) (I k)
      (u k) (v k) (t k) (h k)) atTop (𝓝 Q))
    (ρ : Fin m → ℝ)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ)) :
    (∀ a b, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ r, |Φ r|≤B) →
      spectralOffWardResidual Q ρ (fun a => t₀*lam a) a b Φ=0) ∧
    (∀ a b, spectralDiagonalWardResidual Q ρ (fun a => t₀*lam a) a b=0) := by
  sorry

end InvariantIsing

end

end OAI
end

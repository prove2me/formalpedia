-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorNamespacedArrayLaw_off_ward_limit
-- name    : OAI.InvariantIsing.tensorNamespacedArrayLaw_off_ward_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:45:39.186205+00:00
-- url     : https://prove2.me/theorems/8edac490-1b30-41bd-8d58-b3839ffeda0a
-- title:
--   OAI.InvariantIsing.tensorNamespacedArrayLaw_off_ward_limit: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorNamespacedArrayLaw_off_ward_limit` of [lean/OAI/Probability/InvariantIsing/Arrays/TensorWardLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorWardLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--    theorem tensorNamespacedArrayLaw_off_ward_limit
--       (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
--       (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
--       (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
--       (eig c : (k : ℕ) → Fin (N k) → ℝ)
--       (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
--       (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
--       (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
--       (degree : (k : ℕ) → Fin (N k) → Fin m → ℕ)
--       (treeDegree : (k : ℕ) → Fin (N k) → ℕ)
--       (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k r, |u k r| ≤ 2)
--       (D : ℝ) (hD : 0 ≤ D)
--       (hdegree : ∀ k r, (∑ a, (degree k r a : ℝ)) ≤ D * ((r : ℝ) + 1))
--       (b : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
--       (κ : ℕ → Fin m → ℝ) (hκ : ∀ k a i, i ∈ I k a → eig k i = κ k a)
--       (Q : ProbabilityMeasure (SpectralArray (m + 1)))
--       (hL : Tendsto (fun k => tensorNamespacedArrayLaw (μ k) (eig k) (c k) (I k) (degree k)
--         (tensorPerturbationAmplitude (N k) (u k)) n b (treeDegree k) (h k)) atTop (𝓝 Q))
--       (ρ₀ κ₀ : Fin m → ℝ)
--       (hρ : Tendsto (fun k a => (I k a).card / (N k : ℝ)) atTop (𝓝 ρ₀))
--       (hκlim : Tendsto κ atTop (𝓝 κ₀)) (a b₀ : Fin m)
--       (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (B : ℝ) (hB : 0 ≤ B) (hΦB : ∀ r, |Φ r| ≤ B) :
--       spectralOffWardResidual Q ρ₀ κ₀ a b₀ Φ = 0
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.SpectralArray`, `OAI.InvariantIsing.SpectralEntry` and `OAI.InvariantIsing.tensorPerturbationAmplitude` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.spectralOffWardResidual` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.tensorNamespacedArrayLaw` (definitions bundle `OAIQ258005` of this split).
--
--   **Used by.** The proof of `OAI.InvariantIsing.tensorPerturbedArrayLaw_interactionEnergy_limit` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorWardLimit.lean (declaration OAI.InvariantIsing.tensorNamespacedArrayLaw_off_ward_limit)

import Mathlib
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

 theorem tensorNamespacedArrayLaw_off_ward_limit
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (degree : (k : ℕ) → Fin (N k) → Fin m → ℕ)
    (treeDegree : (k : ℕ) → Fin (N k) → ℕ)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k r, |u k r| ≤ 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ k r, (∑ a, (degree k r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (κ : ℕ → Fin m → ℝ) (hκ : ∀ k a i, i ∈ I k a → eig k i = κ k a)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorNamespacedArrayLaw (μ k) (eig k) (c k) (I k) (degree k)
      (tensorPerturbationAmplitude (N k) (u k)) n b (treeDegree k) (h k)) atTop (𝓝 Q))
    (ρ₀ κ₀ : Fin m → ℝ)
    (hρ : Tendsto (fun k a => (I k a).card / (N k : ℝ)) atTop (𝓝 ρ₀))
    (hκlim : Tendsto κ atTop (𝓝 κ₀)) (a b₀ : Fin m)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (B : ℝ) (hB : 0 ≤ B) (hΦB : ∀ r, |Φ r| ≤ B) :
    spectralOffWardResidual Q ρ₀ κ₀ a b₀ Φ = 0 := by
  sorry

end InvariantIsing

end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorGrowingPerturbedArrayLaw_ward_limits
-- name    : OAI.InvariantIsing.tensorGrowingPerturbedArrayLaw_ward_limits
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:45:24.997084+00:00
-- url     : https://prove2.me/theorems/263b1d3f-434b-4d68-842a-397e35c6c25c
-- title:
--   OAI.InvariantIsing.tensorGrowingPerturbedArrayLaw_ward_limits: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorGrowingPerturbedArrayLaw_ward_limits` of [lean/OAI/Probability/InvariantIsing/Arrays/TensorGrowingPerturbedWard.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorGrowingPerturbedWard.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem tensorGrowingPerturbedArrayLaw_ward_limits
--       (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop) (m : ℕ) (depth : ℕ → ℕ)
--       (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
--       (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
--       (eig c : (k : ℕ) → Fin (N k) → ℝ)
--       (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
--       (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
--       (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
--       (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
--       (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k r, |u k r| ≤ 2)
--       (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a| ≤ 2)
--       (t : ℕ → ℝ) {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀))
--       (b : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
--       (Q : ProbabilityMeasure (SpectralArray (m + 1)))
--       (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
--         (u k) (v k) (t k) (depth k) (b k) (h k)) atTop (𝓝 Q))
--       (ρ : Fin m → ℝ)
--       (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ)) :
--       (∀ a b₀, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ r, |Φ r| ≤ B) →
--         spectralOffWardResidual Q ρ (fun a => t₀ * lam a) a b₀ Φ = 0) ∧
--       (∀ a b₀, spectralDiagonalWardResidual Q ρ (fun a => t₀ * lam a) a b₀ = 0)
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.SpectralArray` and `OAI.InvariantIsing.SpectralEntry` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.spectralDiagonalWardResidual` and `OAI.InvariantIsing.spectralOffWardResidual` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.tensorPerturbedArrayLaw` (definitions bundle `OAIQ258005` of this split).
--
--   **Used by.** The proof of `OAI.InvariantIsing.cavity_fixed_minimum_geometric_limit` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorGrowingPerturbedWard.lean (declaration OAI.InvariantIsing.tensorGrowingPerturbedArrayLaw_ward_limits)

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
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorGrowingPerturbedArrayLaw_ward_limits
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop) (m : ℕ) (depth : ℕ → ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k r, |u k r| ≤ 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a| ≤ 2)
    (t : ℕ → ℝ) {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀))
    (b : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
      (u k) (v k) (t k) (depth k) (b k) (h k)) atTop (𝓝 Q))
    (ρ : Fin m → ℝ)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ)) :
    (∀ a b₀, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ r, |Φ r| ≤ B) →
      spectralOffWardResidual Q ρ (fun a => t₀ * lam a) a b₀ Φ = 0) ∧
    (∀ a b₀, spectralDiagonalWardResidual Q ρ (fun a => t₀ * lam a) a b₀ = 0) := by
  sorry

end InvariantIsing

end

end OAI
end

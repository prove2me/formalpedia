-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_full_tree_cutoff_sequence
-- name    : OAI.InvariantIsing.cavity_full_tree_cutoff_sequence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:21:43.999204+00:00
-- url     : https://prove2.me/theorems/4cee9783-effb-47d2-a8da-b6aab601392e
-- title:
--   OAI.InvariantIsing.cavity_full_tree_cutoff_sequence: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_full_tree_cutoff_sequence` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityFullTreeCutoff.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityFullTreeCutoff.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set`, `open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator`):
--
--   ```lean
--   theorem cavity_full_tree_cutoff_sequence {n m d : ℕ}
--       (N depth : ℕ → ℕ) (hN : ∀ k, 0 < N k + n)
--       (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k + n)))
--       [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
--       (θ : (k : ℕ) → Measure (LabeledTree (depth k))) [∀ k, IsProbabilityMeasure (θ k)]
--       (eig : (k : ℕ) → Fin (N k + n) → ℝ)
--       (g : (k : ℕ) → Fin (N k + n) → Fin m)
--       (u : ℕ → ℕ → ℝ) (hu : ∀ k j, |u k j| ≤ 2)
--       (B : (k : ℕ) → SpecialOrthogonal (N k + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
--       (hmB : ∀ k, Measurable (B k)) (hB : ∀ k U, (B k U).transpose * B k U = 1)
--       (good : (k : ℕ) → Set (SpecialOrthogonal (N k + n)))
--       (hgood : ∀ k, MeasurableSet (good k))
--       (hp : Tendsto (fun k => (μ k).real (good k)) atTop (𝓝 1))
--       {L : ℝ} (hL : 0 < L)
--       (hbound : ∀ k U, U ∈ good k → ∀ a,
--         ‖(CFC.sqrt (cavityCompressionGrams (g k) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
--       (F : (k : ℕ) → (Fin 2 → Spin (N k + n) × LabeledLeaf (depth k)) → ℝ)
--       {M : ℝ} (hM : 0 ≤ M) (hF : ∀ k σ, |F k σ| ≤ M)
--       (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop) :
--       ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ k in atTop,
--         |(∫ T, cavityFullTest (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k) (F k) ∂θ k) -
--           ∫ T, cavityFullCutoffDisorderTest (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k)
--             (cavitySpecialCutoff (g k) (B k) (b j)) (fun _ => F k) ∂θ k| < ε
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.cavityCompressionGrams`, `OAI.InvariantIsing.cavitySpecialOrthogonal` and `OAI.InvariantIsing.cavitySpectralGroup` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityFullCutoffDisorderTest`, `OAI.InvariantIsing.cavityFullTest` and `OAI.InvariantIsing.cavitySpecialCutoff` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree` and `OAI.IsingPerceptron.labeledTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_original_overlap_limit` and `OAI.InvariantIsing.cavity_original_spin_limit` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityFullTreeCutoff.lean (declaration OAI.InvariantIsing.cavity_full_tree_cutoff_sequence)

import Mathlib
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.StrongLaw
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_full_tree_cutoff_sequence {n m d : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ k, 0 < N k + n)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k + n)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (θ : (k : ℕ) → Measure (LabeledTree (depth k))) [∀ k, IsProbabilityMeasure (θ k)]
    (eig : (k : ℕ) → Fin (N k + n) → ℝ)
    (g : (k : ℕ) → Fin (N k + n) → Fin m)
    (u : ℕ → ℕ → ℝ) (hu : ∀ k j, |u k j| ≤ 2)
    (B : (k : ℕ) → SpecialOrthogonal (N k + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hmB : ∀ k, Measurable (B k)) (hB : ∀ k U, (B k U).transpose * B k U = 1)
    (good : (k : ℕ) → Set (SpecialOrthogonal (N k + n)))
    (hgood : ∀ k, MeasurableSet (good k))
    (hp : Tendsto (fun k => (μ k).real (good k)) atTop (𝓝 1))
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ k U, U ∈ good k → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g k) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
    (F : (k : ℕ) → (Fin 2 → Spin (N k + n) × LabeledLeaf (depth k)) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ k σ, |F k σ| ≤ M)
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ k in atTop,
      |(∫ T, cavityFullTest (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k) (F k) ∂θ k) -
        ∫ T, cavityFullCutoffDisorderTest (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k)
          (cavitySpecialCutoff (g k) (B k) (b j)) (fun _ => F k) ∂θ k| < ε := by
  sorry

end InvariantIsing

end

end OAI
end

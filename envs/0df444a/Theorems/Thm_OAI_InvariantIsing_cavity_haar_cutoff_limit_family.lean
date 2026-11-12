-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_haar_cutoff_limit_family
-- name    : OAI.InvariantIsing.cavity_haar_cutoff_limit_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:22:05.021231+00:00
-- url     : https://prove2.me/theorems/90654bc1-a185-45ed-81eb-f50f35dbd6ef
-- title:
--   OAI.InvariantIsing.cavity_haar_cutoff_limit_family: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_haar_cutoff_limit_family` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityHaarCutoffFamily.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityHaarCutoffFamily.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter`, `open scoped Topology Matrix`):
--
--   ```lean
--   theorem cavity_haar_cutoff_limit_family {m d n : ℕ}
--       (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
--       (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
--       (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
--       (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
--       (es : Fin (m*n) ≃ Fin (d+n))
--       (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
--       (l w : ℕ → Fin m → ℕ)
--       (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
--       (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
--       (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
--       [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
--       (ν : (j : ℕ) → Measure (Orthogonal (N j)))
--       [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
--       (T : (j : ℕ) → LabeledTree (depth j)) (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
--       (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ)
--       {D M : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M)
--       (F : (j : ℕ) → (Fin 2 → (Spin (N j) × Spin n) × LabeledLeaf (depth j)) → ℝ)
--       (hF : ∀ j σ, |F j σ| ≤ M) (A₀ : CavityFactorBlocks d n)
--       (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
--         {U | δ < cavityFactorDeviation
--           (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
--             (cavityCompressionGrams (g j) U)) A₀}) atTop (𝓝 0)) :
--       Tendsto (fun j =>
--         (∫ U, cavityOriginalGeometricMean (g j) (cavityConcreteComplement es B₀) (T j)
--           (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
--           (u j) D (F j) (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j) -
--         ∫ V, cavityProjectorCavityMean (T j)
--           (fun a => t*lam a+2*perturbationScale (N j)*v j a) (u j) t D A₀
--           (fun σ => F j (fun i => cavityPairLeafUnswap (σ i)))
--           (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame (k j) (e j) a₀)) ∂ν j)
--         atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` and `OAI.InvariantIsing.CavityFactorBlocks` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.cavityCompressionGrams`, `OAI.InvariantIsing.cavityConcreteComplement`, `OAI.InvariantIsing.cavityOrientationLift`, `OAI.InvariantIsing.cavitySpectralGroup` and `OAI.InvariantIsing.diagonalPerturbedEigenvalues` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityCanonicalProjectorFrame`, `OAI.InvariantIsing.cavityCompressionFactorBlocks`, `OAI.InvariantIsing.cavityFactorDeviation`, `OAI.InvariantIsing.cavityLabeledProjectorAction`, `OAI.InvariantIsing.cavityOriginalGeometricMean`, `OAI.InvariantIsing.cavityPairLeafUnswap` and `OAI.InvariantIsing.cavityProjectorCavityMean` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree` and `OAI.IsingPerceptron.perturbationScale` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Orthogonal` and `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.cavity_original_restricted_haar_limit_family` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityHaarCutoffFamily.lean (declaration OAI.InvariantIsing.cavity_haar_cutoff_limit_family)

import Mathlib
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
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
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

theorem cavity_haar_cutoff_limit_family {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (T : (j : ℕ) → LabeledTree (depth j)) (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ)
    {D M : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × Spin n) × LabeledLeaf (depth j)) → ℝ)
    (hF : ∀ j σ, |F j σ| ≤ M) (A₀ : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A₀}) atTop (𝓝 0)) :
    Tendsto (fun j =>
      (∫ U, cavityOriginalGeometricMean (g j) (cavityConcreteComplement es B₀) (T j)
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
        (u j) D (F j) (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j) -
      ∫ V, cavityProjectorCavityMean (T j)
        (fun a => t*lam a+2*perturbationScale (N j)*v j a) (u j) t D A₀
        (fun σ => F j (fun i => cavityPairLeafUnswap (σ i)))
        (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame (k j) (e j) a₀)) ∂ν j)
      atTop (𝓝 0) := by
  sorry

end InvariantIsing

end

end OAI
end

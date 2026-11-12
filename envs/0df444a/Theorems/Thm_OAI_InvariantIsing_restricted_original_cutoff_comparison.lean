-- Prove2me | Theorems.Thm_OAI_InvariantIsing_restricted_original_cutoff_comparison
-- name    : OAI.InvariantIsing.restricted_original_cutoff_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:32:19.827121+00:00
-- url     : https://prove2.me/theorems/e9f8dea1-6d8c-412c-8787-d86d56dacc83
-- title:
--   OAI.InvariantIsing.restricted_original_cutoff_comparison: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.restricted_original_cutoff_comparison` of [lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedOriginalComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedOriginalComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem restricted_original_cutoff_comparison {N n m depth : ℕ} (hN : 0 < N)
--       (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
--       (U : Rotation (N+n)) (V : Rotation N) (T : LabeledTree depth)
--       (I : Fin m → Finset (Fin (N+n))) (J : Fin m → Finset (Fin N))
--       (eig : Fin (N+n) → ℝ) (eig₀ : Fin N → ℝ)
--       (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
--       (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
--       (w : Spin N × Spin n → ℝ) (hw : ∀ x, 1 ≤ w x)
--       {C D M s₀ : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (hM : 0 ≤ M) (hs₀ : 0 < s₀)
--       (herr : ∀ x y a, |projectedOverlap U (I a) (cavityJoinedSpin x) (cavityJoinedSpin y) -
--         projectedOverlap V (J a) x.1 y.1| ≤ C / N * (w x + w y))
--       (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
--       (hF : ∀ σ, |F σ| ≤ M) :
--       let ν := ((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior Cset hCset)).prod
--         (labeledLeafLaw depth T)
--       let s := {x : (Spin N × Spin n) × LabeledLeaf depth | w x.1 ≤ D}
--       |cavityBaseCutoffReplicaMean U V J eig eig₀ v u t w D (subtypeReference ν s)
--           (fun σ => F (fun i => (σ i).val)) -
--         (∫ z, cavityCutoffReplicaMean
--           (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
--           (cavityRotationHamiltonian U (diagonalPerturbedEigenvalues eig I v t) I u z)
--           {x | w (cavitySpinSplit N n x.1) ≤ D}
--           (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates)| ≤
--         (2 * (2 : ℝ)^2 * (cavityCovarianceRate n C N * (2 * D)) +
--           2 * 2 * (cavityCovarianceRate n C N * (2 * D)) +
--           2 * 2 * (cavityDeterministicRate n m (2 * C) N * D)) / s₀ + M^2 * s₀ / 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.cavityCovarianceRate`, `OAI.InvariantIsing.cavityCutoffReplicaMean`, `OAI.InvariantIsing.cavityDeterministicRate` and `OAI.InvariantIsing.diagonalPerturbedEigenvalues` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityBaseCutoffReplicaMean`, `OAI.InvariantIsing.cavityJoinedSpin`, `OAI.InvariantIsing.cavityProductSlice`, `OAI.InvariantIsing.cavityProductSlice_nonempty`, `OAI.InvariantIsing.cavityRotationHamiltonian`, `OAI.InvariantIsing.cavitySpinSplit`, `OAI.InvariantIsing.projectedOverlap` and `OAI.InvariantIsing.restrictedSpinPrior` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.gaussianCoordinates`, `OAI.IsingPerceptron.labeledLeafLaw`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace`, `OAI.IsingPerceptron.labeledSpinReference` and `OAI.IsingPerceptron.subtypeReference` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Rotation` and `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.restricted_physical_cutoff_comparison` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedOriginalComparison.lean (declaration OAI.InvariantIsing.restricted_original_cutoff_comparison)

import Mathlib
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.Order.Compact
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

theorem restricted_original_cutoff_comparison {N n m depth : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (U : Rotation (N+n)) (V : Rotation N) (T : LabeledTree depth)
    (I : Fin m → Finset (Fin (N+n))) (J : Fin m → Finset (Fin N))
    (eig : Fin (N+n) → ℝ) (eig₀ : Fin N → ℝ)
    (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    (w : Spin N × Spin n → ℝ) (hw : ∀ x, 1 ≤ w x)
    {C D M s₀ : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (hM : 0 ≤ M) (hs₀ : 0 < s₀)
    (herr : ∀ x y a, |projectedOverlap U (I a) (cavityJoinedSpin x) (cavityJoinedSpin y) -
      projectedOverlap V (J a) x.1 y.1| ≤ C / N * (w x + w y))
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    let ν := ((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior Cset hCset)).prod
      (labeledLeafLaw depth T)
    let s := {x : (Spin N × Spin n) × LabeledLeaf depth | w x.1 ≤ D}
    |cavityBaseCutoffReplicaMean U V J eig eig₀ v u t w D (subtypeReference ν s)
        (fun σ => F (fun i => (σ i).val)) -
      (∫ z, cavityCutoffReplicaMean
        (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
        (cavityRotationHamiltonian U (diagonalPerturbedEigenvalues eig I v t) I u z)
        {x | w (cavitySpinSplit N n x.1) ≤ D}
        (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates)| ≤
      (2 * (2 : ℝ)^2 * (cavityCovarianceRate n C N * (2 * D)) +
        2 * 2 * (cavityCovarianceRate n C N * (2 * D)) +
        2 * 2 * (cavityDeterministicRate n m (2 * C) N * D)) / s₀ + M^2 * s₀ / 2 := by
  sorry

end InvariantIsing

end

end OAI
end

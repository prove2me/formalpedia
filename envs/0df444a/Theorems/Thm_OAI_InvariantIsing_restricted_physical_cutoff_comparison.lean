-- Prove2me | Theorems.Thm_OAI_InvariantIsing_restricted_physical_cutoff_comparison
-- name    : OAI.InvariantIsing.restricted_physical_cutoff_comparison
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:42:33.258195+00:00
-- url     : https://prove2.me/theorems/be1ae63b-4cef-4f77-bbaf-adb8beac4a69
-- title:
--   OAI.InvariantIsing.restricted_physical_cutoff_comparison: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.restricted_physical_cutoff_comparison` of [lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedPhysicalCutoffComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedPhysicalCutoffComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped Matrix`):
--
--   ```lean
--   theorem restricted_physical_cutoff_comparison {N n m d depth : ℕ} (hN : 0 < N)
--       (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
--       (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
--       (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
--       (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
--       (es : Fin (m*n) ≃ Fin (d+n))
--       (U : SpecialOrthogonal (N+n)) (lam : Fin m → ℝ) (a₀ : Fin d → Fin m)
--       (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
--       (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
--         B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
--       (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
--         cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
--       (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
--       (T : LabeledTree depth) (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
--       (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
--       {D M s : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M) (hs : 0 < s)
--       (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
--       (hF : ∀ σ, |F σ| ≤ M) :
--       let G := cavityCompressionGrams g (cavitySpecialOrthogonal U)
--       let B₁ := B G
--       let A := cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
--         (Matrix.diagonal (fun j => lam (a₀ j))) B₁ (cavitySpectralStack G)
--       let p := cavityPhysicalLabeledProjectors g B a₀ (cavitySpecialOrthogonal U)
--       let w := cavityGeometricWeight g B₁ U
--       |restrictedProjectorCavityMean S hS Cset hCset T (fun a => t*lam a+2*perturbationScale N*v a)
--           u t D A (fun σ => F (fun i => cavityPairLeafUnswap (σ i))) p -
--         (∫ z, cavityCutoffReplicaMean
--           (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
--           (cavityRotationHamiltonian (specialRotation U)
--             (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
--             (cavitySpectralGroup g) u z)
--           {x | w (cavitySpinSplit N n x.1) ≤ D}
--           (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates)| ≤
--         (2 * (2 : ℝ)^2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
--           2 * 2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
--           2 * 2 * (cavityDeterministicRate n m (2*(2*n+1)) N * D)) / s + M^2*s/2
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.CavityFactorBlocks` and `OAI.InvariantIsing.CavityProjectorFrame` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.cavityCompressionGrams`, `OAI.InvariantIsing.cavityCovarianceRate`, `OAI.InvariantIsing.cavityCutoffReplicaMean`, `OAI.InvariantIsing.cavityDeterministicRate`, `OAI.InvariantIsing.cavityRepeatedSpectrum`, `OAI.InvariantIsing.cavitySpecialOrthogonal`, `OAI.InvariantIsing.cavitySpectralGroup`, `OAI.InvariantIsing.cavitySpectralStack`, `OAI.InvariantIsing.diagonalPerturbedEigenvalues` and `OAI.InvariantIsing.specialRotation` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityGeometricWeight`, `OAI.InvariantIsing.cavityPairLeafUnswap`, `OAI.InvariantIsing.cavityPhysicalLabeledProjectors`, `OAI.InvariantIsing.cavityProductSlice`, `OAI.InvariantIsing.cavityProductSlice_nonempty`, `OAI.InvariantIsing.cavityRotationHamiltonian`, `OAI.InvariantIsing.cavitySmallFactorBlocks`, `OAI.InvariantIsing.cavitySpinSplit` and `OAI.InvariantIsing.restrictedSpinPrior` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.restrictedProjectorCavityMean` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.gaussianCoordinates`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace`, `OAI.IsingPerceptron.labeledSpinReference` and `OAI.IsingPerceptron.perturbationScale` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.restricted_haar_cutoff_limit` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedPhysicalCutoffComparison.lean (declaration OAI.InvariantIsing.restricted_physical_cutoff_comparison)

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
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem restricted_physical_cutoff_comparison {N n m d depth : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (U : SpecialOrthogonal (N+n)) (lam : Fin m → ℝ) (a₀ : Fin d → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (T : LabeledTree depth) (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    {D M s : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M) (hs : 0 < s)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    let G := cavityCompressionGrams g (cavitySpecialOrthogonal U)
    let B₁ := B G
    let A := cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
      (Matrix.diagonal (fun j => lam (a₀ j))) B₁ (cavitySpectralStack G)
    let p := cavityPhysicalLabeledProjectors g B a₀ (cavitySpecialOrthogonal U)
    let w := cavityGeometricWeight g B₁ U
    |restrictedProjectorCavityMean S hS Cset hCset T (fun a => t*lam a+2*perturbationScale N*v a)
        u t D A (fun σ => F (fun i => cavityPairLeafUnswap (σ i))) p -
      (∫ z, cavityCutoffReplicaMean
        (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
        (cavityRotationHamiltonian (specialRotation U)
          (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
          (cavitySpectralGroup g) u z)
        {x | w (cavitySpinSplit N n x.1) ≤ D}
        (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates)| ≤
      (2 * (2 : ℝ)^2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
        2 * 2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
        2 * 2 * (cavityDeterministicRate n m (2*(2*n+1)) N * D)) / s + M^2*s/2 := by
  sorry

end InvariantIsing

end

end OAI
end

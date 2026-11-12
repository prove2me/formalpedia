-- Prove2me | Theorems.Thm_OAI_InvariantIsing_restricted_tree_pressure_capped_increment
-- name    : OAI.InvariantIsing.restricted_tree_pressure_capped_increment
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:42:48.786806+00:00
-- url     : https://prove2.me/theorems/2a1b4be3-4f51-4f42-9914-6012085acdd4
-- title:
--   OAI.InvariantIsing.restricted_tree_pressure_capped_increment: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.restricted_tree_pressure_capped_increment` of [lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedTreePressureIncrement.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedTreePressureIncrement.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`):
--
--   ```lean
--   theorem restricted_tree_pressure_capped_increment {N n m d depth : ℕ} (hN : 0<N)
--       (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
--       (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
--       (ek : ∀ a, {i : Fin (N+n) // g i=a} ≃ Fin (k a+n))
--       (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
--       (es : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
--       (a₀ : Fin d → Fin m) (l r : Fin m → ℕ)
--       (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val < r a)
--       (hln : ∀ a, l a+n ≤ r a) (hr : ∀ a, r a ≤ N+n)
--       (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
--       (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
--       (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ] (lam v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
--       (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap) :
--       let A := fun U => cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
--         (cavityCompressionGrams g U)
--       let q := fun V => cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)
--       let c := fun a => t*lam a+2*perturbationScale N*v a
--       let δ := cavityDeterministicRate n m (2*(2*n+1)) N+
--         2*cavityCovarianceRate n (2*n+1) N
--       let I₀ := cavityBaseGroup k e a₀
--       let eig₀ := diagonalPerturbedEigenvalues
--         (fun i => lam (Sum.elim (fun w => w.1) a₀ (e.symm i))) I₀ v t
--       let I := cavitySpectralGroup g
--       let eig := diagonalPerturbedEigenvalues (fun i => lam (g i)) I v t
--       (∫ T, ∫ z, restrictedProjectorCappedLog S hS C hC T c u t cap δ (A z.1) (q z.2)
--         ∂μ.prod ν ∂θ) ≤
--         (∫ z, restrictedRotationLogMean (cavityProductSlice S C) (cavityProductSlice_nonempty S hS C hC) z.2 eig I u z.1 ∂μ.prod θ) -
--           ∫ z, restrictedRotationLogMean S hS z.2 eig₀ I₀ u z.1 ∂ν.prod θ
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace`, `OAI.InvariantIsing.CavityFactorBlocks` and `OAI.InvariantIsing.CavityProjectorFrame` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.cavityBaseGroup`, `OAI.InvariantIsing.cavityCompressionGrams`, `OAI.InvariantIsing.cavityCovarianceRate`, `OAI.InvariantIsing.cavityDeterministicRate`, `OAI.InvariantIsing.cavitySpectralGroup` and `OAI.InvariantIsing.diagonalPerturbedEigenvalues` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityCanonicalProjectorFrame`, `OAI.InvariantIsing.cavityCompressionFactorBlocks`, `OAI.InvariantIsing.cavityLabeledProjectorAction`, `OAI.InvariantIsing.cavityProductSlice`, `OAI.InvariantIsing.cavityProductSlice_nonempty` and `OAI.InvariantIsing.restrictedRotationLogMean` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.restrictedProjectorCappedLog` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.labeledTreeMeasurableSpace` and `OAI.IsingPerceptron.perturbationScale` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Orthogonal` and `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.restricted_physical_trial_lower` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedTreePressureIncrement.lean (declaration OAI.InvariantIsing.restricted_tree_pressure_capped_increment)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem restricted_tree_pressure_capped_increment {N n m d depth : ℕ} (hN : 0<N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i=a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) (l r : Fin m → ℕ)
    (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val < r a)
    (hln : ∀ a, l a+n ≤ r a) (hr : ∀ a, r a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ] (lam v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap) :
    let A := fun U => cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
      (cavityCompressionGrams g U)
    let q := fun V => cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)
    let c := fun a => t*lam a+2*perturbationScale N*v a
    let δ := cavityDeterministicRate n m (2*(2*n+1)) N+
      2*cavityCovarianceRate n (2*n+1) N
    let I₀ := cavityBaseGroup k e a₀
    let eig₀ := diagonalPerturbedEigenvalues
      (fun i => lam (Sum.elim (fun w => w.1) a₀ (e.symm i))) I₀ v t
    let I := cavitySpectralGroup g
    let eig := diagonalPerturbedEigenvalues (fun i => lam (g i)) I v t
    (∫ T, ∫ z, restrictedProjectorCappedLog S hS C hC T c u t cap δ (A z.1) (q z.2)
      ∂μ.prod ν ∂θ) ≤
      (∫ z, restrictedRotationLogMean (cavityProductSlice S C) (cavityProductSlice_nonempty S hS C hC) z.2 eig I u z.1 ∂μ.prod θ) -
        ∫ z, restrictedRotationLogMean S hS z.2 eig₀ I₀ u z.1 ∂ν.prod θ := by
  sorry

end InvariantIsing

end

end OAI
end

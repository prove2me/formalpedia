-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_haar_finite_cutoff_comparison
-- name    : OAI.InvariantIsing.cavity_haar_finite_cutoff_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:34:14.803043+00:00
-- url     : https://prove2.me/theorems/2c6b1bb2-800a-4db3-af51-25c5c2349b19
-- title:
--   OAI.InvariantIsing.cavity_haar_finite_cutoff_comparison: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_haar_finite_cutoff_comparison` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityHaarFiniteCutoff.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityHaarFiniteCutoff.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set`, `open scoped BigOperators Topology BoundedContinuousFunction`):
--
--   ```lean
--   theorem cavity_haar_finite_cutoff_comparison {m r q dim kspin : ℕ}
--       (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
--       (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
--       [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
--       (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
--       (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
--       (Ω X : ℕ → Type*) [∀ k, MeasurableSpace (Ω k)] [∀ k, MeasurableSpace (X k)]
--       [∀ k, Countable (X k)] [∀ k, MeasurableSingletonClass (X k)]
--       (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
--       (ν : (k : ℕ) → Ω k → Measure (X k)) (hν : ∀ k, Measurable (ν k))
--       [∀ k ω, IsProbabilityMeasure (ν k ω)]
--       (B : (k : ℕ) → Ω k → X k → X k → SpectralEntry (m + 1))
--       (hB : ∀ k x y, Measurable (fun ω => B k ω x y))
--       (hGram : ∀ k x, SpectralGram (cavitySampledEntryArray (B k) x))
--       (v₀ : (k : ℕ) → Ω k → (j : Fin m) → X k → Fin (N k j) → ℝ)
--       (hvM : ∀ k x, Measurable (fun ω j => v₀ k ω j x))
--       (C : ℝ)
--       (hv : ∀ s k (x : Ω k × (ℕ → X k)) j (i l : Fin s), |cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i)) j i l| ≤ C)
--       (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
--       (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
--       (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
--       (hcov : ∀ s k (x : Ω k × (ℕ → X k)), cavityGroupReplicaCovariance q (cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i))) =
--         cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) s (cavitySampledEntryArray (B k) x)))
--       (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
--       (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
--       (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (disorderReplicaLaw (P k) (ν k) (hν k)).map (cavitySampledEntryArray (B k)))
--       (hlim : Tendsto Q atTop (𝓝 Q₀))
--       (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m + 1))))
--       (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
--       (d : Fin (m + 1) → ℝ) (hd0 : ∀ j, 0 ≤ d j)
--       (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = d j)
--       (hE : ∀ e : ℕ → ℕ, Function.Injective e →
--         (Q₀ : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q₀)
--       (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
--       (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
--       (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
--         spectralOffWardResidual Q₀ ρ eig j l Φ = 0)
--       (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ eig j l = 0)
--       (g : Fin dim → Fin m) (e : Fin dim → Fin m × Fin q)
--       (he : Function.Injective e) (heg : ∀ j, (e j).1 = g j)
--       (K : Matrix (Fin dim) (Fin dim) ℝ) (L : Matrix (Fin dim) (Fin kspin) ℝ)
--       (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ)
--       (π : Measure (Spin kspin)) [IsProbabilityMeasure π]
--       (Fspin : SpectralBlock m r × (Fin r → Spin kspin) →ᵇ ℝ)
--       (hNpos : ∀ n a, 0 < N n a) (hC : 0 ≤ C)
--       {N₀ : ℕ} (B₀ : Matrix (Fin (m*N₀)) (Fin dim) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
--       (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
--       (hK : K = B₀.transpose * cavityRepeatedSpectrum (n := N₀) eig * B₀ -
--         Matrix.diagonal (fun i => eig (g i)))
--       (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop)
--       (hnull : ∀ j s, (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m s) : Measure
--         (SpectralBlock m s × EuclideanSpace ℝ (Fin m × (Fin s × Fin q))))
--         {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0) :
--       let p := spectralSpinQuantilePath Q₀ hP hn
--       let τ := fun j => cavityFactorSize K L Cspin * (1+(b j)^2)
--       let η := fun n => cavityLabeledPriorKernel n
--         (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p n)
--           (cavityStrictUniformLevels p n) n) π
--       let Qf := fun n => cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
--         (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p n)
--           (cavityStrictUniformLevels p n))
--         (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p n)
--           (uniformCut n) (cavityStrictUniformLevels p n))
--       let Of := fun n => cavityFiniteReplicaSpectralBlock ρ eig hρ hρsum (cavityStrictUniformPath p n)
--         (cavityStrictUniformLevels p n)
--       ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop,
--         |(∫ ω, cavityWeightedReplicaMean ((ν n ω.1).prod π)
--             (fun x => cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin (τ j) (b j) (ω,x))
--             (cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1) Fspin)
--             ∂(P n).prod (Measure.pi (μ n))) -
--           ∫ ω, cavityWeightedReplicaMean (η n ω)
--             (fun x => Real.exp (cavityLabeledPotential n K L Cspin (ω,x)))
--             (fun σ => cavityLabeledReplicaTest (Of n) Fspin (ω,σ)) ∂Qf n| < ε
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace`, `OAI.InvariantIsing.CavityLabeledDisorder` and `OAI.InvariantIsing.CavityLabeledState` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpectralArray`, `OAI.InvariantIsing.SpectralBlock`, `OAI.InvariantIsing.SpectralEntry`, `OAI.InvariantIsing.SpectralGram`, `OAI.InvariantIsing.SpectralPartitionGeometry`, `OAI.InvariantIsing.cavityFactorSize`, `OAI.InvariantIsing.cavityGroupReplicaCovariance`, `OAI.InvariantIsing.cavityGroupReplicaGram`, `OAI.InvariantIsing.cavityRepeatedSpectrum`, `OAI.InvariantIsing.cavityReplicaRadius`, `OAI.InvariantIsing.cavitySampledEntryArray`, `OAI.InvariantIsing.cavitySampledGroupBlock`, `OAI.InvariantIsing.cavitySelectedGroupProjection`, `OAI.InvariantIsing.cavitySpectralBlockCovariance`, `OAI.InvariantIsing.cavitySpectralGroupBlock`, `OAI.InvariantIsing.cavityWeightedReplicaMean`, `OAI.InvariantIsing.disorderReplicaLaw` and `OAI.InvariantIsing.spectralBlockView` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityBlockMarkedLaw`, `OAI.InvariantIsing.cavityFiniteCovariancePath`, `OAI.InvariantIsing.cavityFiniteNoiseCovariance`, `OAI.InvariantIsing.cavityFiniteReplicaSpectralBlock`, `OAI.InvariantIsing.cavityFiniteRootCovariance`, `OAI.InvariantIsing.cavityHaarRestrictedWeight`, `OAI.InvariantIsing.cavityLabeledDisorderLaw`, `OAI.InvariantIsing.cavityLabeledPotential`, `OAI.InvariantIsing.cavityLabeledPriorKernel`, `OAI.InvariantIsing.cavityLabeledReplicaTest`, `OAI.InvariantIsing.cavityProjectedSpinTest`, `OAI.InvariantIsing.cavityStrictUniformLevels` and `OAI.InvariantIsing.cavityStrictUniformPath` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.permuteSpectralArray`, `OAI.InvariantIsing.spectralDiagonalWardResidual` and `OAI.InvariantIsing.spectralOffWardResidual` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.spectralSpinQuantilePath` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.ForestVertex`, `OAI.IsingPerceptron.HasEntryGhirlandaGuerra`, `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.chainExponent`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace`, `OAI.IsingPerceptron.labeledTreeMeasurableSpace` and `OAI.IsingPerceptron.uniformCut` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Orthogonal`, `OAI.InvariantIsing.OverlapPath` and `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_original_overlap_limit`, `OAI.InvariantIsing.cavity_physical_spin_cutoff`, `OAI.InvariantIsing.restricted_original_spin_limit` and `OAI.InvariantIsing.restricted_original_split_overlap_limit` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityHaarFiniteCutoff.lean (declaration OAI.InvariantIsing.cavity_haar_finite_cutoff_comparison)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_finite_cutoff_comparison {m r q dim kspin : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (Ω X : ℕ → Type*) [∀ k, MeasurableSpace (Ω k)] [∀ k, MeasurableSpace (X k)]
    [∀ k, Countable (X k)] [∀ k, MeasurableSingletonClass (X k)]
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (ν : (k : ℕ) → Ω k → Measure (X k)) (hν : ∀ k, Measurable (ν k))
    [∀ k ω, IsProbabilityMeasure (ν k ω)]
    (B : (k : ℕ) → Ω k → X k → X k → SpectralEntry (m + 1))
    (hB : ∀ k x y, Measurable (fun ω => B k ω x y))
    (hGram : ∀ k x, SpectralGram (cavitySampledEntryArray (B k) x))
    (v₀ : (k : ℕ) → Ω k → (j : Fin m) → X k → Fin (N k j) → ℝ)
    (hvM : ∀ k x, Measurable (fun ω j => v₀ k ω j x))
    (C : ℝ)
    (hv : ∀ s k (x : Ω k × (ℕ → X k)) j (i l : Fin s), |cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i)) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ s k (x : Ω k × (ℕ → X k)), cavityGroupReplicaCovariance q (cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i))) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) s (cavitySampledEntryArray (B k) x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (disorderReplicaLaw (P k) (ν k) (hν k)).map (cavitySampledEntryArray (B k)))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (d : Fin (m + 1) → ℝ) (hd0 : ∀ j, 0 ≤ d j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = d j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ eig j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ eig j l = 0)
    (g : Fin dim → Fin m) (e : Fin dim → Fin m × Fin q)
    (he : Function.Injective e) (heg : ∀ j, (e j).1 = g j)
    (K : Matrix (Fin dim) (Fin dim) ℝ) (L : Matrix (Fin dim) (Fin kspin) ℝ)
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ)
    (π : Measure (Spin kspin)) [IsProbabilityMeasure π]
    (Fspin : SpectralBlock m r × (Fin r → Spin kspin) →ᵇ ℝ)
    (hNpos : ∀ n a, 0 < N n a) (hC : 0 ≤ C)
    {N₀ : ℕ} (B₀ : Matrix (Fin (m*N₀)) (Fin dim) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (hK : K = B₀.transpose * cavityRepeatedSpectrum (n := N₀) eig * B₀ -
      Matrix.diagonal (fun i => eig (g i)))
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop)
    (hnull : ∀ j s, (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m s) : Measure
      (SpectralBlock m s × EuclideanSpace ℝ (Fin m × (Fin s × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let τ := fun j => cavityFactorSize K L Cspin * (1+(b j)^2)
    let η := fun n => cavityLabeledPriorKernel n
      (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n) n) π
    let Qf := fun n => cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
      (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n))
      (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p n)
        (uniformCut n) (cavityStrictUniformLevels p n))
    let Of := fun n => cavityFiniteReplicaSpectralBlock ρ eig hρ hρsum (cavityStrictUniformPath p n)
      (cavityStrictUniformLevels p n)
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      |(∫ ω, cavityWeightedReplicaMean ((ν n ω.1).prod π)
          (fun x => cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin (τ j) (b j) (ω,x))
          (cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1) Fspin)
          ∂(P n).prod (Measure.pi (μ n))) -
        ∫ ω, cavityWeightedReplicaMean (η n ω)
          (fun x => Real.exp (cavityLabeledPotential n K L Cspin (ω,x)))
          (fun σ => cavityLabeledReplicaTest (Of n) Fspin (ω,σ)) ∂Qf n| < ε := by
  sorry

end InvariantIsing

end

end OAI
end

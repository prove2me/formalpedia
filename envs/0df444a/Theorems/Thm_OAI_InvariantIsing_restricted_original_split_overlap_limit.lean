-- Prove2me | Theorems.Thm_OAI_InvariantIsing_restricted_original_split_overlap_limit
-- name    : OAI.InvariantIsing.restricted_original_split_overlap_limit
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:43:16.564576+00:00
-- url     : https://prove2.me/theorems/ddb1daa9-65b8-4d2c-9d8a-92608c2ac1be
-- title:
--   OAI.InvariantIsing.restricted_original_split_overlap_limit: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.restricted_original_split_overlap_limit` of [lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedOriginalOverlapLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedOriginalOverlapLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set`, `open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators`):
--
--   ```lean
--   theorem restricted_original_split_overlap_limit (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {m d n : ℕ}
--       (N depth : ℕ → ℕ)
--       (S : (j : ℕ) → Finset (Spin (N j))) (hS : ∀ j, (S j).Nonempty)
--       (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
--       (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
--       (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
--       (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
--       (es : Fin (m*n) ≃ Fin (d+n))
--       (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
--       (hk : ∀ j a, d ≤ k j a)
--       (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
--       [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
--       (l w : ℕ → Fin m → ℕ)
--       (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
--       (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
--       (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
--       [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
--       (ν : (j : ℕ) → Measure (Orthogonal (N j)))
--       [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
--       (θ : (j : ℕ) → Measure (LabeledTree (depth j))) [∀ j, IsProbabilityMeasure (θ j)]
--       (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
--       (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2)
--       {M₀ : ℝ} (hmean : ∀ j (T : LabeledTree (depth j)), restrictedCavityFullDisorderTest
--         (cavityProductSlice (S j) Cset) (cavityProductSlice_nonempty (S j) (hS j) Cset hCset)
--         ((μ j).map (cavityOrientationLift (Nat.add_pos_left (hN j) n))) T
--         (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) 1)
--         (cavitySpectralGroup (g j)) (u j)
--         (cavityProjectionAxesTest (cavitySpectralGroup (g j)) (Fin.natAdd (N j))) ≤ M₀)
--       (good : (j : ℕ) → Set (SpecialOrthogonal (N j+n)))
--       (hgood : ∀ j, MeasurableSet (good j))
--       (hp : Tendsto (fun j => ((μ j).map (cavityOrientationLift
--         (Nat.add_pos_left (hN j) n))).real (good j)) atTop (𝓝 1))
--       {L : ℝ} (hL : 0 < L)
--       (hbound : ∀ j U, U ∈ good j → ∀ a,
--         ‖(CFC.sqrt (cavityCompressionGrams (g j) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
--       (hd : 0 < d) (hn : 0 < n)
--       (hB₀ : B₀.transpose * B₀ = 1)
--       (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
--       (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
--       (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
--       (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
--       {c : ℝ} (hc : 0 < c)
--       (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j)
--       (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j) atTop (𝓝 ρ))
--       (A : CavityFactorBlocks d n)
--       (hA : A = ((cavityCompressionLimitFrame es B₀).transpose *
--         cavityRepeatedSpectrum (n := n) lam * cavityCompressionLimitFrame es B₀ -
--         Matrix.diagonal (fun i => lam (a₀ i)),
--         (cavityCompressionLimitFrame es B₀).transpose * cavityRepeatedSpectrum (n := n) lam *
--           cavityLimitingStack (n := n) ρ,
--         (finiteR ρ lam hρ hρsum 0) • (1 : Matrix (Fin n) (Fin n) ℝ)))
--       (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
--         {U | δ < cavityFactorDeviation
--           (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
--             (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0))
--       (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
--       (hlim : Tendsto (fun j => restrictedRotationArrayLaw (S j) (hS j) (ν j) (θ j)
--         (diagonalPerturbedEigenvalues
--           (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)
--           (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (v j) 1)
--         (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (u j))
--         atTop (𝓝 Q₀))
--       (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m+1))))
--       (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralGram x)
--       (δ : Fin (m+1) → ℝ) (hδ0 : ∀ j, 0 ≤ δ j)
--       (hδ : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ i j, (x (i,i) j : ℝ) = δ j)
--       (hE : ∀ e : ℕ → ℕ, Function.Injective e →
--         (Q₀ : Measure (SpectralArray (m+1))).map (permuteSpectralArray e) = Q₀)
--       (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x)
--       (hnonneg : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
--       (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
--         spectralOffWardResidual Q₀ ρ lam j l Φ = 0)
--       (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ lam j l = 0)
--       (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
--       (Φ : ℝ →ᵇ ℝ) :
--       let p := spectralSpinQuantilePath Q₀ hP hnonneg
--       Tendsto (fun r =>
--         (∫ T, restrictedFullTest (cavityProductSlice (S r) Cset) (cavityProductSlice_nonempty (S r) (hS r) Cset hCset) ((μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))) T
--           (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
--           (cavitySpectralGroup (g r)) (u r) (cavitySplitOverlapInsertion Φ) ∂θ r) -
--         ∫ t, Φ (cavityStrictUniformPath p r t) ∂pathMeasure)
--         atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` and `OAI.InvariantIsing.CavityFactorBlocks` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.SpectralArray`, `OAI.InvariantIsing.SpectralEntry`, `OAI.InvariantIsing.SpectralGram`, `OAI.InvariantIsing.SpectralPartitionGeometry`, `OAI.InvariantIsing.cavityBaseGroupDimension`, `OAI.InvariantIsing.cavityBaseGroupEquiv`, `OAI.InvariantIsing.cavityCompressionGrams`, `OAI.InvariantIsing.cavityCompressionLimitFrame`, `OAI.InvariantIsing.cavityLimitingStack`, `OAI.InvariantIsing.cavityOrientationLift`, `OAI.InvariantIsing.cavityReindexedStack`, `OAI.InvariantIsing.cavityRepeatedSpectrum`, `OAI.InvariantIsing.cavitySpecialOrthogonal`, `OAI.InvariantIsing.cavitySpectralGroup`, `OAI.InvariantIsing.diagonalPerturbedEigenvalues` and `OAI.InvariantIsing.finiteR` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.PanchenkoTalagrandRestrictedFieldPairInput`, `OAI.InvariantIsing.cavityCompressionFactorBlocks`, `OAI.InvariantIsing.cavityFactorDeviation`, `OAI.InvariantIsing.cavityProductSlice`, `OAI.InvariantIsing.cavityProductSlice_nonempty`, `OAI.InvariantIsing.cavityProjectionAxesTest`, `OAI.InvariantIsing.cavitySplitOverlapInsertion` and `OAI.InvariantIsing.cavityStrictUniformPath` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.permuteSpectralArray`, `OAI.InvariantIsing.spectralDiagonalWardResidual` and `OAI.InvariantIsing.spectralOffWardResidual` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.restrictedCavityFullDisorderTest`, `OAI.InvariantIsing.restrictedFullTest`, `OAI.InvariantIsing.restrictedRotationArrayLaw` and `OAI.InvariantIsing.spectralSpinQuantilePath` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.HasEntryGhirlandaGuerra`, `OAI.IsingPerceptron.LabeledTree` and `OAI.IsingPerceptron.labeledTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Orthogonal`, `OAI.InvariantIsing.OverlapPath`, `OAI.InvariantIsing.Spin` and `OAI.InvariantIsing.pathMeasure` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.offset_product_weak_self_consistency` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedOriginalOverlapLimit.lean (declaration OAI.InvariantIsing.restricted_original_split_overlap_limit)

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
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators

namespace InvariantIsing

theorem restricted_original_split_overlap_limit (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {m d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (j : ℕ) → Finset (Spin (N j))) (hS : ∀ j, (S j).Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : (j : ℕ) → Measure (LabeledTree (depth j))) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2)
    {M₀ : ℝ} (hmean : ∀ j (T : LabeledTree (depth j)), restrictedCavityFullDisorderTest
      (cavityProductSlice (S j) Cset) (cavityProductSlice_nonempty (S j) (hS j) Cset hCset)
      ((μ j).map (cavityOrientationLift (Nat.add_pos_left (hN j) n))) T
      (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) 1)
      (cavitySpectralGroup (g j)) (u j)
      (cavityProjectionAxesTest (cavitySpectralGroup (g j)) (Fin.natAdd (N j))) ≤ M₀)
    (good : (j : ℕ) → Set (SpecialOrthogonal (N j+n)))
    (hgood : ∀ j, MeasurableSet (good j))
    (hp : Tendsto (fun j => ((μ j).map (cavityOrientationLift
      (Nat.add_pos_left (hN j) n))).real (good j)) atTop (𝓝 1))
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ j U, U ∈ good j → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g j) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
    (hd : 0 < d) (hn : 0 < n)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
    (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
    (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
    {c : ℝ} (hc : 0 < c)
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j)
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j) atTop (𝓝 ρ))
    (A : CavityFactorBlocks d n)
    (hA : A = ((cavityCompressionLimitFrame es B₀).transpose *
      cavityRepeatedSpectrum (n := n) lam * cavityCompressionLimitFrame es B₀ -
      Matrix.diagonal (fun i => lam (a₀ i)),
      (cavityCompressionLimitFrame es B₀).transpose * cavityRepeatedSpectrum (n := n) lam *
        cavityLimitingStack (n := n) ρ,
      (finiteR ρ lam hρ hρsum 0) • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun j => restrictedRotationArrayLaw (S j) (hS j) (ν j) (θ j)
      (diagonalPerturbedEigenvalues
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (v j) 1)
      (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (u j))
      atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m+1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralGram x)
    (δ : Fin (m+1) → ℝ) (hδ0 : ∀ j, 0 ≤ δ j)
    (hδ : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ i j, (x (i,i) j : ℝ) = δ j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m+1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x)
    (hnonneg : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ lam j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ lam j l = 0)
    (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (Φ : ℝ →ᵇ ℝ) :
    let p := spectralSpinQuantilePath Q₀ hP hnonneg
    Tendsto (fun r =>
      (∫ T, restrictedFullTest (cavityProductSlice (S r) Cset) (cavityProductSlice_nonempty (S r) (hS r) Cset hCset) ((μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))) T
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
        (cavitySpectralGroup (g r)) (u r) (cavitySplitOverlapInsertion Φ) ∂θ r) -
      ∫ t, Φ (cavityStrictUniformPath p r t) ∂pathMeasure)
      atTop (𝓝 0) := by
  sorry

end InvariantIsing

end

end OAI
end

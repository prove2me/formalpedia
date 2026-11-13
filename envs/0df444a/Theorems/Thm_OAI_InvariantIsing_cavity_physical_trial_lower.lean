-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_physical_trial_lower
-- name    : OAI.InvariantIsing.cavity_physical_trial_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:36:22.393044+00:00
-- url     : https://prove2.me/theorems/3febf14b-f92b-4877-ace0-5ef8f5f7fe70
-- title:
--   OAI.InvariantIsing.cavity_physical_trial_lower: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_physical_trial_lower` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityPhysicalTrialLower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityPhysicalTrialLower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter`, `open scoped Topology BigOperators`):
--
--   ```lean
--   theorem cavity_physical_trial_lower {m d n : ℕ} (hn₀ : 0<n)
--       (N depth : ℕ → ℕ) (hN : ∀ r, 0<N r) (hNlim : Tendsto N atTop atTop)
--       (g : (r : ℕ) → Fin (N r+n) → Fin m) (k : ℕ → Fin m → ℕ)
--       (e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r))
--       (ek : ∀ r a, {i : Fin (N r+n) // g r i=a} ≃ Fin (k r a+n))
--       (es : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
--       (l w : Fin m → ℕ → ℕ)
--       (hg : ∀ r a i, g r i=a ↔ l a r ≤ i.val ∧ i.val<w a r)
--       (hln : ∀ r a, l a r+n ≤ w a r) (hw : ∀ r a, w a r ≤ N r+n)
--       (a₀ : Fin d → Fin m) (hk : ∀ r a, d ≤ k r a)
--       (hgroups : ∀ r a, 0 < cavityBaseGroupDimension (k r) a₀ a)
--       (hdims : ∀ a, Tendsto (fun r => cavityBaseGroupDimension (k r) a₀ a) atTop atTop)
--       (μ : (r : ℕ) → Measure (Orthogonal (N r+n))) [∀ r, IsProbabilityMeasure (μ r)] [∀ r, (μ r).IsMulRightInvariant]
--       (ν : (r : ℕ) → Measure (Orthogonal (N r))) [∀ r, IsProbabilityMeasure (ν r)] [∀ r, (ν r).IsMulRightInvariant]
--       (θ : (r : ℕ) → Measure (LabeledTree (depth r))) [∀ r, IsProbabilityMeasure (θ r)]
--       (μG : (r : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k r) a₀ a)))
--       [∀ r a, IsProbabilityMeasure (μG r a)] [∀ r a, (μG r a).IsMulRightInvariant]
--       (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ) (u : ℕ → ℕ → ℝ)
--       (hv : ∀ r a, |v r a|≤2) (hu : ∀ r j, |u r j|≤2)
--       {c : ℝ} (hc : 0 < c)
--       (hfrac : ∀ r a, c ≤ (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r)
--       (ρ : Fin m → ℝ) (hρ : ∀ a, 0<ρ a) (hρsum : ∑ a, ρ a=1)
--       (hρlim : Tendsto (fun r a => (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r) atTop (𝓝 ρ))
--       (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
--       (hlim : Tendsto (fun r => cavityRotationArrayLaw (ν r) (θ r)
--         (diagonalPerturbedEigenvalues
--           (fun i => lam ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1)
--           (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1)) (v r) 1)
--         (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1))
--         (u r)) atTop (𝓝 Q₀))
--       (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m+1))))
--       (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralGram x)
--       (d₀ : Fin (m+1) → ℝ) (hd0 : ∀ j, 0≤d₀ j)
--       (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ i j, (x (i,i) j : ℝ)=d₀ j)
--       (hE : ∀ e : ℕ → ℕ, Function.Injective e →
--         (Q₀ : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q₀)
--       (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x)
--       (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ j, 0≤(x (0,1) j : ℝ))
--       (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ t, |Φ t|≤B) →
--         spectralOffWardResidual Q₀ ρ lam j l Φ=0)
--       (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ lam j l=0)
--       (B : Matrix (Fin (m*n)) (Fin d) ℝ) (hB : B.transpose*B=1)
--       (hBE : B.transpose*cavityLimitingStack (n := n) ρ=0)
--       (hcomplete : B*B.transpose+cavityLimitingStack (n := n) ρ*
--         (cavityLimitingStack (n := n) ρ).transpose=1)
--       (amax : Fin m) (hmax : ∀ a, lam a≤lam amax)
--       (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a≤n)
--       (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
--       (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) (R : Rotation n)
--       (hprob : ∀ ε>0, Tendsto (fun r => (μ r).real {U | ε < cavityFactorDeviation
--         (cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
--           (cavityCompressionGrams (g r) U))
--         (B.transpose*cavityRepeatedSpectrum (n := n) lam*B-Matrix.diagonal (fun j => lam (a₀ j)),
--          B.transpose*cavityRepeatedSpectrum (n := n) lam*cavityLimitingStack (n := n) ρ,
--          (finiteR ρ lam hρ hρsum 0) • 1)}) atTop (𝓝 0)) :
--       let p := spectralSpinQuantilePath Q₀ hP hn
--       let Δ := fun r =>
--         (∫ z, cavityRotationLogMean z.2
--           (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
--           (cavitySpectralGroup (g r)) (u r) z.1 ∂(μ r).prod (θ r)) -
--         ∫ z, cavityRotationLogMean z.2
--           (diagonalPerturbedEigenvalues
--             (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e r).symm i)))
--             (cavityBaseGroup (k r) (e r) a₀) (v r) 1)
--           (cavityBaseGroup (k r) (e r) a₀) (u r) z.1 ∂(ν r).prod (θ r)
--       ∀ ε>0, ∀ᶠ r in atTop,
--         fieldValue (cavityStrictUniformField ρ lam hρ hρsum p r) 0+
--           fieldPairing (cavityStrictUniformPath p r) (cavityStrictUniformField ρ lam hρ hρsum p r)/2+
--           spectralFunctional (finiteR ρ lam hρ hρsum) (cavityStrictUniformPath p r)-
--           (n : ℝ)⁻¹*Δ r < ε
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpectralArray`, `OAI.InvariantIsing.SpectralEntry`, `OAI.InvariantIsing.SpectralGram`, `OAI.InvariantIsing.SpectralPartitionGeometry`, `OAI.InvariantIsing.cavityBaseGroup`, `OAI.InvariantIsing.cavityBaseGroupDimension`, `OAI.InvariantIsing.cavityBaseGroupEquiv`, `OAI.InvariantIsing.cavityCompressionGrams`, `OAI.InvariantIsing.cavityLimitingStack`, `OAI.InvariantIsing.cavityRepeatedSpectrum`, `OAI.InvariantIsing.cavitySpectralGroup`, `OAI.InvariantIsing.diagonalPerturbedEigenvalues` and `OAI.InvariantIsing.finiteR` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityCompressionFactorBlocks`, `OAI.InvariantIsing.cavityFactorDeviation`, `OAI.InvariantIsing.cavityRotationArrayLaw`, `OAI.InvariantIsing.cavityRotationLogMean`, `OAI.InvariantIsing.cavityStrictUniformField` and `OAI.InvariantIsing.cavityStrictUniformPath` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.permuteSpectralArray`, `OAI.InvariantIsing.spectralDiagonalWardResidual` and `OAI.InvariantIsing.spectralOffWardResidual` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.spectralSpinQuantilePath` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.HasEntryGhirlandaGuerra`, `OAI.IsingPerceptron.LabeledTree` and `OAI.IsingPerceptron.labeledTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Orthogonal`, `OAI.InvariantIsing.OverlapPath`, `OAI.InvariantIsing.Rotation`, `OAI.InvariantIsing.fieldPairing`, `OAI.InvariantIsing.fieldValue` and `OAI.InvariantIsing.spectralFunctional` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.cavity_window_minimum_variational_lower` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityPhysicalTrialLower.lean (declaration OAI.InvariantIsing.cavity_physical_trial_lower)

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
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
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

attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_physical_trial_lower {m d n : ℕ} (hn₀ : 0<n)
    (N depth : ℕ → ℕ) (hN : ∀ r, 0<N r) (hNlim : Tendsto N atTop atTop)
    (g : (r : ℕ) → Fin (N r+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r))
    (ek : ∀ r a, {i : Fin (N r+n) // g r i=a} ≃ Fin (k r a+n))
    (es : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (l w : Fin m → ℕ → ℕ)
    (hg : ∀ r a i, g r i=a ↔ l a r ≤ i.val ∧ i.val<w a r)
    (hln : ∀ r a, l a r+n ≤ w a r) (hw : ∀ r a, w a r ≤ N r+n)
    (a₀ : Fin d → Fin m) (hk : ∀ r a, d ≤ k r a)
    (hgroups : ∀ r a, 0 < cavityBaseGroupDimension (k r) a₀ a)
    (hdims : ∀ a, Tendsto (fun r => cavityBaseGroupDimension (k r) a₀ a) atTop atTop)
    (μ : (r : ℕ) → Measure (Orthogonal (N r+n))) [∀ r, IsProbabilityMeasure (μ r)] [∀ r, (μ r).IsMulRightInvariant]
    (ν : (r : ℕ) → Measure (Orthogonal (N r))) [∀ r, IsProbabilityMeasure (ν r)] [∀ r, (ν r).IsMulRightInvariant]
    (θ : (r : ℕ) → Measure (LabeledTree (depth r))) [∀ r, IsProbabilityMeasure (θ r)]
    (μG : (r : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k r) a₀ a)))
    [∀ r a, IsProbabilityMeasure (μG r a)] [∀ r a, (μG r a).IsMulRightInvariant]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ) (u : ℕ → ℕ → ℝ)
    (hv : ∀ r a, |v r a|≤2) (hu : ∀ r j, |u r j|≤2)
    {c : ℝ} (hc : 0 < c)
    (hfrac : ∀ r a, c ≤ (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0<ρ a) (hρsum : ∑ a, ρ a=1)
    (hρlim : Tendsto (fun r a => (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r) atTop (𝓝 ρ))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun r => cavityRotationArrayLaw (ν r) (θ r)
      (diagonalPerturbedEigenvalues
        (fun i => lam ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1)) (v r) 1)
      (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1))
      (u r)) atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m+1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralGram x)
    (d₀ : Fin (m+1) → ℝ) (hd0 : ∀ j, 0≤d₀ j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ i j, (x (i,i) j : ℝ)=d₀ j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ j, 0≤(x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ t, |Φ t|≤B) →
      spectralOffWardResidual Q₀ ρ lam j l Φ=0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ lam j l=0)
    (B : Matrix (Fin (m*n)) (Fin d) ℝ) (hB : B.transpose*B=1)
    (hBE : B.transpose*cavityLimitingStack (n := n) ρ=0)
    (hcomplete : B*B.transpose+cavityLimitingStack (n := n) ρ*
      (cavityLimitingStack (n := n) ρ).transpose=1)
    (amax : Fin m) (hmax : ∀ a, lam a≤lam amax)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a≤n)
    (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) (R : Rotation n)
    (hprob : ∀ ε>0, Tendsto (fun r => (μ r).real {U | ε < cavityFactorDeviation
      (cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
        (cavityCompressionGrams (g r) U))
      (B.transpose*cavityRepeatedSpectrum (n := n) lam*B-Matrix.diagonal (fun j => lam (a₀ j)),
       B.transpose*cavityRepeatedSpectrum (n := n) lam*cavityLimitingStack (n := n) ρ,
       (finiteR ρ lam hρ hρsum 0) • 1)}) atTop (𝓝 0)) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let Δ := fun r =>
      (∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
        (cavitySpectralGroup (g r)) (u r) z.1 ∂(μ r).prod (θ r)) -
      ∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues
          (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e r).symm i)))
          (cavityBaseGroup (k r) (e r) a₀) (v r) 1)
        (cavityBaseGroup (k r) (e r) a₀) (u r) z.1 ∂(ν r).prod (θ r)
    ∀ ε>0, ∀ᶠ r in atTop,
      fieldValue (cavityStrictUniformField ρ lam hρ hρsum p r) 0+
        fieldPairing (cavityStrictUniformPath p r) (cavityStrictUniformField ρ lam hρ hρsum p r)/2+
        spectralFunctional (finiteR ρ lam hρ hρsum) (cavityStrictUniformPath p r)-
        (n : ℝ)⁻¹*Δ r < ε := by
  sorry

end InvariantIsing

end

end OAI
end

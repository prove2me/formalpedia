-- Prove2me | Theorems.Thm_OAI_InvariantIsing_offset_window_minimum_trial_witness
-- name    : OAI.InvariantIsing.offset_window_minimum_trial_witness
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:40:33.478646+00:00
-- url     : https://prove2.me/theorems/aa320dc4-c666-4336-a656-e20b226f7046
-- title:
--   OAI.InvariantIsing.offset_window_minimum_trial_witness: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.offset_window_minimum_trial_witness` of [lean/OAI/Probability/InvariantIsing/Cavity/OffsetWindowTrialWitness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/OffsetWindowTrialWitness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set`, `open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators`):
--
--   ```lean
--   theorem offset_window_minimum_trial_witness (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
--       (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {m d n r₀ : ℕ}
--       (K : ℕ → ℕ) (hK : ∀ j, 2 ≤ K j) (hKlim : Tendsto K atTop atTop)
--       (R : Finset (Spin r₀)) (hR : R.Nonempty)
--       (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (hN : ∀ j, 0 < r₀+K j*n) (hNlim : Tendsto (fun j => r₀+K j*n) atTop atTop)
--       (hN3 : ∀ j, 3 ≤ r₀+K j*n)
--       (g : (j : ℕ) → Fin (r₀+K j*n+n) → Fin m) (k : ℕ → Fin m → ℕ)
--       (ek : ∀ j a, {i : Fin (r₀+K j*n+n) // g j i = a} ≃ Fin (k j a+n))
--       (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (r₀+K j*n))
--       (es : Fin (m*n) ≃ Fin (d+n))
--       (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
--       (hk : ∀ j a, d ≤ k j a)
--       (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
--       [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
--       (l w : ℕ → Fin m → ℕ)
--       (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
--       (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ r₀+K j*n+n)
--       (μ : (j : ℕ) → Measure (Orthogonal (r₀+K j*n+n)))
--       [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
--       (ν : (j : ℕ) → Measure (Orthogonal (r₀+K j*n)))
--       [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
--       (θ : ℕ → Measure (LabeledTree 0)) [∀ j, IsProbabilityMeasure (θ j)]
--       (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
--       (hv : ∀ j a, v j a∈Set.Icc (1 : ℝ) 2)
--       (u : (j : ℕ) → Fin (r₀+K j*n) → ℝ) (hu : ∀ j i, u j i∈Set.Icc (1 : ℝ) 2)
--       (hmin : ∀ j u' v', (∀ i, u' i∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
--         priorPerturbationObjective (cavityOrientedBaseLaw (hN j) (ν j))
--           (restrictedZeroTreePrior (offsetBlockConstraint (K j) R Cset)
--             (offsetBlockConstraint_nonempty R hR Cset hCset))
--           (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
--           (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
--           1 (fun _ => 0) (u j) (v j) ≤
--         priorPerturbationObjective (cavityOrientedBaseLaw (hN j) (ν j))
--           (restrictedZeroTreePrior (offsetBlockConstraint (K j) R Cset)
--             (offsetBlockConstraint_nonempty R hR Cset hCset))
--           (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
--           (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
--           1 (fun _ => 0) u' v')
--       (hd : 0 < d) (hn : 0 < n)
--       (hB₀ : B₀.transpose * B₀ = 1)
--       (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
--       (ρl ρw : Fin m → ℝ) (hρdef : ρ=fun a => ρw a-ρl a)
--       (hwlim : ∀ a, Tendsto (fun j => w j a) atTop atTop)
--       (hllim : ∀ a, (∀ j, l j a=0) ∨ Tendsto (fun j => l j a) atTop atTop)
--       (hρl : ∀ a, Tendsto (fun j => (l j a : ℝ)/(r₀+K j*n+n : ℕ)) atTop (𝓝 (ρl a)))
--       (hρw : ∀ a, Tendsto (fun j => (w j a : ℝ)/(r₀+K j*n+n : ℕ)) atTop (𝓝 (ρw a)))
--       (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
--       (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
--       (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
--       {c : ℝ} (hc : 0 < c)
--       (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/((r₀+K j*n : ℕ) : ℝ))
--       (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/((r₀+K j*n : ℕ) : ℝ)) atTop (𝓝 ρ))
--       (amax : Fin m) (hmax : ∀ a, lam a≤lam amax)
--       (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a ≤ n)
--       (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
--       (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) :
--       let Δ := fun j =>
--         (∫ z, restrictedRotationLogMean
--           (cavityProductSlice (offsetBlockConstraint (K j) R Cset) Cset)
--           (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR Cset hCset) Cset hCset) z.2
--           (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) 1)
--           (cavitySpectralGroup (g j)) (cavityBaseAmplitude (u j)) z.1 ∂(μ j).prod (θ j)) -
--         ∫ z, restrictedRotationLogMean (offsetBlockConstraint (K j) R Cset)
--           (offsetBlockConstraint_nonempty R hR Cset hCset) z.2
--           (diagonalPerturbedEigenvalues
--             (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e j).symm i)))
--             (cavityBaseGroup (k j) (e j) a₀) (v j) 1)
--           (cavityBaseGroup (k j) (e j) a₀) (cavityBaseAmplitude (u j)) z.1 ∂(ν j).prod (θ j)
--
--       ∃ (p : OverlapPath) (φ : ℕ → ℕ), StrictMono φ ∧
--         (∀ Φ : ℝ →ᵇ ℝ,
--           Tendsto (fun r => ∫ t, Φ (cavityStrictUniformPath p r t) *
--             (restrictedBlockOverlapPath hn Cset hCset (cavityStrictUniformField ρ lam hρ hρsum p r) t -
--               cavityStrictUniformPath p r t) ∂pathMeasure) atTop (𝓝 0)) ∧
--         ∀ ε > 0, ∀ᶠ r in atTop,
--           constrainedBlockValue Cset (cavityStrictUniformField ρ lam hρ hρsum p r)+
--             fieldPairing (cavityStrictUniformPath p r) (cavityStrictUniformField ρ lam hρ hρsum p r)/2+
--             spectralFunctional (finiteR ρ lam hρ hρsum) (cavityStrictUniformPath p r)-
--             (n : ℝ)⁻¹*(Δ (φ r)+(Real.log Cset.card-n*Real.log 2)) < ε
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput`, `OAI.InvariantIsing.cavityBaseAmplitude`, `OAI.InvariantIsing.cavityBaseGroup`, `OAI.InvariantIsing.cavityBaseGroupDimension`, `OAI.InvariantIsing.cavityBaseGroupEquiv`, `OAI.InvariantIsing.cavityReindexedStack`, `OAI.InvariantIsing.cavitySpectralGroup`, `OAI.InvariantIsing.diagonalPerturbedEigenvalues` and `OAI.InvariantIsing.finiteR` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.HaarConcentrationInput`, `OAI.InvariantIsing.PanchenkoTalagrandRestrictedFieldPairInput`, `OAI.InvariantIsing.cavityOrientedBaseLaw`, `OAI.InvariantIsing.cavityProductSlice`, `OAI.InvariantIsing.cavityProductSlice_nonempty`, `OAI.InvariantIsing.cavityStrictUniformField`, `OAI.InvariantIsing.cavityStrictUniformPath`, `OAI.InvariantIsing.constrainedBlockValue`, `OAI.InvariantIsing.offsetBlockConstraint`, `OAI.InvariantIsing.offsetBlockConstraint_nonempty`, `OAI.InvariantIsing.priorPerturbationObjective`, `OAI.InvariantIsing.restrictedRotationLogMean` and `OAI.InvariantIsing.restrictedZeroTreePrior` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.restrictedBlockOverlapPath` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.LabeledTree` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Orthogonal`, `OAI.InvariantIsing.OverlapPath`, `OAI.InvariantIsing.Spin`, `OAI.InvariantIsing.fieldPairing`, `OAI.InvariantIsing.pathMeasure` and `OAI.InvariantIsing.spectralFunctional` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.magnetic_affine_increment_eventually_lower` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/OffsetWindowTrialWitness.lean (declaration OAI.InvariantIsing.offset_window_minimum_trial_witness)

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
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
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

attribute [-instance] _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators
namespace InvariantIsing

theorem offset_window_minimum_trial_witness (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {m d n r₀ : ℕ}
    (K : ℕ → ℕ) (hK : ∀ j, 2 ≤ K j) (hKlim : Tendsto K atTop atTop)
    (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (hN : ∀ j, 0 < r₀+K j*n) (hNlim : Tendsto (fun j => r₀+K j*n) atTop atTop)
    (hN3 : ∀ j, 3 ≤ r₀+K j*n)
    (g : (j : ℕ) → Fin (r₀+K j*n+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (r₀+K j*n+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (r₀+K j*n))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ r₀+K j*n+n)
    (μ : (j : ℕ) → Measure (Orthogonal (r₀+K j*n+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (r₀+K j*n)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : ℕ → Measure (LabeledTree 0)) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, v j a∈Set.Icc (1 : ℝ) 2)
    (u : (j : ℕ) → Fin (r₀+K j*n) → ℝ) (hu : ∀ j i, u j i∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ j u' v', (∀ i, u' i∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective (cavityOrientedBaseLaw (hN j) (ν j))
        (restrictedZeroTreePrior (offsetBlockConstraint (K j) R Cset)
          (offsetBlockConstraint_nonempty R hR Cset hCset))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 (fun _ => 0) (u j) (v j) ≤
      priorPerturbationObjective (cavityOrientedBaseLaw (hN j) (ν j))
        (restrictedZeroTreePrior (offsetBlockConstraint (K j) R Cset)
          (offsetBlockConstraint_nonempty R hR Cset hCset))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 (fun _ => 0) u' v')
    (hd : 0 < d) (hn : 0 < n)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (ρl ρw : Fin m → ℝ) (hρdef : ρ=fun a => ρw a-ρl a)
    (hwlim : ∀ a, Tendsto (fun j => w j a) atTop atTop)
    (hllim : ∀ a, (∀ j, l j a=0) ∨ Tendsto (fun j => l j a) atTop atTop)
    (hρl : ∀ a, Tendsto (fun j => (l j a : ℝ)/(r₀+K j*n+n : ℕ)) atTop (𝓝 (ρl a)))
    (hρw : ∀ a, Tendsto (fun j => (w j a : ℝ)/(r₀+K j*n+n : ℕ)) atTop (𝓝 (ρw a)))
    (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
    (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
    (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
    {c : ℝ} (hc : 0 < c)
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/((r₀+K j*n : ℕ) : ℝ))
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/((r₀+K j*n : ℕ) : ℝ)) atTop (𝓝 ρ))
    (amax : Fin m) (hmax : ∀ a, lam a≤lam amax)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a ≤ n)
    (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) :
    let Δ := fun j =>
      (∫ z, restrictedRotationLogMean
        (cavityProductSlice (offsetBlockConstraint (K j) R Cset) Cset)
        (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR Cset hCset) Cset hCset) z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) 1)
        (cavitySpectralGroup (g j)) (cavityBaseAmplitude (u j)) z.1 ∂(μ j).prod (θ j)) -
      ∫ z, restrictedRotationLogMean (offsetBlockConstraint (K j) R Cset)
        (offsetBlockConstraint_nonempty R hR Cset hCset) z.2
        (diagonalPerturbedEigenvalues
          (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e j).symm i)))
          (cavityBaseGroup (k j) (e j) a₀) (v j) 1)
        (cavityBaseGroup (k j) (e j) a₀) (cavityBaseAmplitude (u j)) z.1 ∂(ν j).prod (θ j)

    ∃ (p : OverlapPath) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ Φ : ℝ →ᵇ ℝ,
        Tendsto (fun r => ∫ t, Φ (cavityStrictUniformPath p r t) *
          (restrictedBlockOverlapPath hn Cset hCset (cavityStrictUniformField ρ lam hρ hρsum p r) t -
            cavityStrictUniformPath p r t) ∂pathMeasure) atTop (𝓝 0)) ∧
      ∀ ε > 0, ∀ᶠ r in atTop,
        constrainedBlockValue Cset (cavityStrictUniformField ρ lam hρ hρsum p r)+
          fieldPairing (cavityStrictUniformPath p r) (cavityStrictUniformField ρ lam hρ hρsum p r)/2+
          spectralFunctional (finiteR ρ lam hρ hρsum) (cavityStrictUniformPath p r)-
          (n : ℝ)⁻¹*(Δ (φ r)+(Real.log Cset.card-n*Real.log 2)) < ε := by
  sorry

end InvariantIsing

end

end OAI
end

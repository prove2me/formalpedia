-- Prove2me | Theorems.Thm_OAI_Erdos970_NumberTheoryLean_RetainedOccupationLimit_retained_original_occupation_limit_jb247
-- name    : OAI.Erdos970.NumberTheoryLean.RetainedOccupationLimit.retained_original_occupation_limit_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T19:06:48.122347+00:00
-- url     : https://prove2.me/theorems/d7fac423-7bb4-45ac-aa6b-182df6fa2e0f
-- title:
--   OAI.Erdos970.NumberTheoryLean.RetainedOccupationLimit.retained_original_occupation_limit_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.NumberTheoryLean.RetainedOccupationLimit.retained_original_occupation_limit` of [lean/OAI/NumberTheory/Jacobsthal/Renewal/RetainedOccupationLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Renewal/RetainedOccupationLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.NumberTheoryLean.RetainedOccupationLimit`, with `open scoped _root_.Erdos970`, `open _root_.Set _root_.Filter _root_.MeasureTheory`, `open scoped Topology`, `open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership`, `open LiteralPrimeOccupation CompactInverseTest`, `open CompactLogOccupationTest`, `open SignedCompactTransfer NormalizedOccupationLimit LowStateHorizon`):
--
--   ```lean
--   theorem retained_original_occupation_limit_jb247 {H : Side → ℝ×ℝ → ℝ}
--       (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
--       {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 1 ≤ ell)
--       (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0)
--       (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
--       ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
--         Real.log B ≤ d*Real.log w → ∀ start : Node,
--           start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
--           Consistent start → start.cutoff=B →
--           |familyValue H w ell ((Real.log B)^2) start-invariantAverage (arrivalTest ell H)| ≤ ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.NumberTheoryLean.FinitePathGeometry.Side` (definitions bundle `OAIQ247J001` of this split); `OAI.Erdos970.NumberTheoryLean.CompactLogOccupationTest.arrivalTest`, `OAI.Erdos970.NumberTheoryLean.NormalizedOccupationLimit.invariantAverage` and `OAI.Erdos970.NumberTheoryLean.PrimeHistories.Node` (definitions bundle `OAIQ247J007` of this split); `OAI.Erdos970.NumberTheoryLean.LiteralPrimeOccupation.familyValue` and `OAI.Erdos970.NumberTheoryLean.PrimeBinMembership.Consistent` (definitions bundle `OAIQ247J010` of this split).
--
--   **Used by.** The proofs of `OAI.Erdos970.ErdosCorrectionLimit.floored_source_correction_tendsto_jb247`, `OAI.Erdos970.ErdosSourceReferenceMargin.root_anomaly_replacement_tendsto_jb247`, `OAI.Erdos970.NumberTheoryLean.GeometricTotalBoxMass.uniform_geometric_box_mass_jb247`, `OAI_Erdos970_NumberTheoryLean_GlobalSafeTagCapture_global_bad_tag_mass_small_jb247`, `OAI.Erdos970.NumberTheoryLean.PaperRegularTagCapture.paper_regular_bad_tag_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.StoppedErrorReduction.stopped_error_reduction_jb247` and `OAI.Erdos970.NumberTheoryLean.UniformBoundaryCorrection.uniform_boundary_correction_div_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Renewal/RetainedOccupationLimit.lean (declaration OAI.Erdos970.NumberTheoryLean.RetainedOccupationLimit.retained_original_occupation_limit)

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_OAIQ247J010

section

attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.RetainedOccupationLimit

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open LiteralPrimeOccupation CompactInverseTest
open CompactLogOccupationTest
open SignedCompactTransfer NormalizedOccupationLimit LowStateHorizon

theorem retained_original_occupation_limit_jb247 {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 1 ≤ ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0)
    (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |familyValue H w ell ((Real.log B)^2) start-invariantAverage (arrivalTest ell H)| ≤ ε := by
  sorry

end NumberTheoryLean.RetainedOccupationLimit

end

end Erdos970

end OAI
end

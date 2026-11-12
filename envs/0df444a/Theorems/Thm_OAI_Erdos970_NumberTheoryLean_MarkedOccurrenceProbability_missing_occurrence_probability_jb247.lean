-- Prove2me | Theorems.Thm_OAI_Erdos970_NumberTheoryLean_MarkedOccurrenceProbability_missing_occurrence_probability_jb247
-- name    : OAI.Erdos970.NumberTheoryLean.MarkedOccurrenceProbability.missing_occurrence_probability_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T19:05:40.024522+00:00
-- url     : https://prove2.me/theorems/2ef076c3-50ea-45ef-ab93-46bbea5cd7ba
-- title:
--   OAI.Erdos970.NumberTheoryLean.MarkedOccurrenceProbability.missing_occurrence_probability_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.NumberTheoryLean.MarkedOccurrenceProbability.missing_occurrence_probability` of [lean/OAI/NumberTheory/Jacobsthal/Probability/MarkedOccurrenceProbability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Probability/MarkedOccurrenceProbability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.NumberTheoryLean.MarkedOccurrenceProbability`, with `open scoped _root_.Erdos970`, `open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory`, `open scoped ENNReal`, `open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership`, `open ActualCoupledHistories ActualProcessCoupling FlaggedSourceStart`, `open FiniteHistoryTransport PriorPrimeWindow CompactPrefixOccurrence CompletedMarkEvents`, `open ContinuousKilledBins PersistentFailureFlag`, `open Erdos970Dependency.MarkedVisits`):
--
--   ```lean
--   theorem missing_occurrence_probability_jb247 (hc : Consistent start)
--       (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hR : (11/10)*R < 6*b₀)
--       {mesh : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1/100) (N : ℕ)
--       (herror : 4*(N:ℝ)*mesh ≤ Real.log (11/10)) (E : Set (List ℕ))
--       (hE : ∀ p : History w ell S start,p.primes ∈ E →
--         p.node.gap ≤ R ∧ ¬hasPrimeWindow w b₀ b₁ start p.primes) :
--       sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N {h | occurs E N h} ≤
--         sourceLaw hw hell hS0 hS hr hs hsS mesh N failed +
--         finitePathMeasure (typedState start.side start.ratio hs) N
--           (closedNoHitEvent 1 N start.gap b₀ b₁ 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.NumberTheoryLean.FinitePathMeasures.CostState`, `OAI.Erdos970.NumberTheoryLean.FinitePathMeasures.State`, `OAI.Erdos970.NumberTheoryLean.TransitionKernels.EvenState` and `OAI.Erdos970.NumberTheoryLean.TransitionKernels.OddState` (definitions bundle `OAIQ247J001` of this split); `OAI.Erdos970.NumberTheoryLean.CemeteryKernel.Space`, `OAI.Erdos970.NumberTheoryLean.FiniteHistoryTransport.Hist`, `OAI.Erdos970.NumberTheoryLean.PersistentFailureFlag.FlagState` and `OAI.Erdos970.NumberTheoryLean.PersistentFailureFlag.failed` (definitions bundle `OAIQ247J003` of this split); `OAI.Erdos970.Erdos970Dependency.MarkedVisits.closedNoHitEvent`, `OAI.Erdos970.NumberTheoryLean.FinitePathGeometry.Valid`, `OAI.Erdos970.NumberTheoryLean.FinitePathMeasures.finitePathMeasure`, `OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.typedState`, `OAI.Erdos970.NumberTheoryLean.PrimeHistories.History`, `OAI.Erdos970.NumberTheoryLean.PrimeHistories.Node`, `OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.ChainState`, `OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState` and `OAI.Erdos970.NumberTheoryLean.PrimeHistories.History.node` (definitions bundle `OAIQ247J007` of this split); `OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceHistoryLaw`, `OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.JointState` and `OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.normalizationThreshold` (definitions bundle `OAIQ247J008` of this split); `OAI.Erdos970.NumberTheoryLean.CompactPrefixOccurrence.occurs`, `OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.sourceLaw`, `OAI.Erdos970.NumberTheoryLean.PrimeBinMembership.Consistent` and `OAI.Erdos970.NumberTheoryLean.PriorPrimeWindow.hasPrimeWindow` (definitions bundle `OAIQ247J010` of this split).
--
--   **Used by.** The proof of `OAI.Erdos970.NumberTheoryLean.MovingPrimeWindowProbability.source_missing_window_probability_jb247` of this split imports it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Probability/MarkedOccurrenceProbability.lean (declaration OAI.Erdos970.NumberTheoryLean.MarkedOccurrenceProbability.missing_occurrence_probability)

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
import Definitions.Def_OAIQ247J010

section

attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarkedOccurrenceProbability

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualCoupledHistories ActualProcessCoupling FlaggedSourceStart
open FiniteHistoryTransport PriorPrimeWindow CompactPrefixOccurrence CompletedMarkEvents
open ContinuousKilledBins PersistentFailureFlag
open Erdos970Dependency.MarkedVisits

variable {w ell S R b₀ b₁ : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem missing_occurrence_probability_jb247 (hc : Consistent start)
    (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hR : (11/10)*R < 6*b₀)
    {mesh : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1/100) (N : ℕ)
    (herror : 4*(N:ℝ)*mesh ≤ Real.log (11/10)) (E : Set (List ℕ))
    (hE : ∀ p : History w ell S start,p.primes ∈ E →
      p.node.gap ≤ R ∧ ¬hasPrimeWindow w b₀ b₁ start p.primes) :
    sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N {h | occurs E N h} ≤
      sourceLaw hw hell hS0 hS hr hs hsS mesh N failed +
      finitePathMeasure (typedState start.side start.ratio hs) N
        (closedNoHitEvent 1 N start.gap b₀ b₁ 1) := by
  sorry

end NumberTheoryLean.MarkedOccurrenceProbability

end

end Erdos970

end OAI
end

-- Prove2me | Theorems.Thm_OAI_Erdos970_NumberTheoryLean_SourceCouplingRate_source_coupling_rate_jb247
-- name    : OAI.Erdos970.NumberTheoryLean.SourceCouplingRate.source_coupling_rate_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:31.349615+00:00
-- url     : https://prove2.me/theorems/92692216-a5b1-4390-9535-08183a95a794
-- title:
--   OAI.Erdos970.NumberTheoryLean.SourceCouplingRate.source_coupling_rate_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.NumberTheoryLean.SourceCouplingRate.source_coupling_rate` of [lean/OAI/NumberTheory/Jacobsthal/Probability/SourceCompactCoupling.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Probability/SourceCompactCoupling.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.NumberTheoryLean.SourceCouplingRate`, with `open scoped _root_.Erdos970`, `open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory`, `open scoped ENNReal Topology`, `open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership`, `open UniformFailureBudget ActualFlagInvariant`, `open PersistentFailureFlag LowStateHorizon ExponentialMesh`):
--
--   ```lean
--   theorem source_coupling_rate_jb247 : ∃ κ₀ : ℝ, 0 < κ₀ ∧
--       ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ d : ℝ, 0 < d → ∃ w₀ : ℝ, 1 < w₀ ∧
--       ∀ w : ℝ, w₀ ≤ w → ∀ ell B : ℝ, ∀ start : Node, ∀ hs : Valid start.side start.ratio,
--         1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
--         0 < start.gap → start.ratio ≤ 23/10 → Consistent start → start.gap ≤ (23/10:ℝ)*B →
--         let S := (Real.log B)^2
--         let N := sourceHorizon S B
--         (∀ n ≤ N,
--           CouplingData.sourceLaw w ell S start hs (mesh κ w) n failed ≤
--             ENNReal.ofReal (Real.exp (-(κ/2)*Real.sqrt (Real.log w))) ∧
--           ∀ᵐ q ∂CouplingData.sourceLaw w ell S start hs (mesh κ w) n,
--             q.2 = false → GoodAt (Real.log start.gap) (mesh κ w) n q.1) ∧
--         (∀ᵐ q ∂CouplingData.sourceLaw w ell S start hs (mesh κ w) N,
--           q.2 = false → q.1 = (none,CemeteryKernel.dead))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.NumberTheoryLean.FinitePathMeasures.CostState`, `OAI.Erdos970.NumberTheoryLean.FinitePathMeasures.State`, `OAI.Erdos970.NumberTheoryLean.TransitionKernels.EvenState` and `OAI.Erdos970.NumberTheoryLean.TransitionKernels.OddState` (definitions bundle `OAIQ247J001` of this split); `OAI.Erdos970.NumberTheoryLean.CemeteryKernel.Space`, `OAI.Erdos970.NumberTheoryLean.CemeteryKernel.dead`, `OAI.Erdos970.NumberTheoryLean.ExponentialMesh.mesh`, `OAI.Erdos970.NumberTheoryLean.LowStateHorizon.sourceHorizon`, `OAI.Erdos970.NumberTheoryLean.PersistentFailureFlag.FlagState` and `OAI.Erdos970.NumberTheoryLean.PersistentFailureFlag.failed` (definitions bundle `OAIQ247J003` of this split); `OAI.Erdos970.NumberTheoryLean.FinitePathGeometry.Valid`, `OAI.Erdos970.NumberTheoryLean.PrimeHistories.History`, `OAI.Erdos970.NumberTheoryLean.PrimeHistories.Node`, `OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.ChainState` and `OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState` (definitions bundle `OAIQ247J007` of this split); `OAI.Erdos970.NumberTheoryLean.ActualFlagInvariant.GoodAt` and `OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.JointState` (definitions bundle `OAIQ247J008` of this split); `OAI.Erdos970.NumberTheoryLean.CouplingData.sourceLaw` and `OAI.Erdos970.NumberTheoryLean.PrimeBinMembership.Consistent` (definitions bundle `OAIQ247J010` of this split).
--
--   **Used by.** The proofs of `OAI_Erdos970_NumberTheoryLean_CorrectedCompactTransfer_source_corrected_compact_transfer_jb247`, `OAI_Erdos970_NumberTheoryLean_CorrectedCompactTransfer_source_inverse_compact_transfer_jb247`, `OAI.Erdos970.NumberTheoryLean.MovingPrimeWindowProbability.source_missing_window_probability_jb247`, `OAI_Erdos970_NumberTheoryLean_ReferenceIsolatedExclusion_uniform_reference_nonisolated_mass_jb247`, `OAI.Erdos970.NumberTheoryLean.RetainedOccupationLimit.retained_original_occupation_limit_jb247`, `OAI.Erdos970.NumberTheoryLean.ScaledOriginalTail.actual_uniform_scaled_tail_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceIsolatedProbability.source_nonisolated_probability_jb247`, `OAI_Erdos970_NumberTheoryLean_SourceModerateFailure_source_moderate_failure_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceRepeatedRates.source_repeated_pair_probabilities_jb247`, `OAI.Erdos970.NumberTheoryLean.SourceThresholdRate.source_prime_threshold_probability_jb247` and `OAI_Erdos970_NumberTheoryLean_WeightedNearThreshold_weighted_near_threshold_prefix_mass_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Probability/SourceCompactCoupling.lean (declaration OAI.Erdos970.NumberTheoryLean.SourceCouplingRate.source_coupling_rate)

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

attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceCouplingRate

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open UniformFailureBudget ActualFlagInvariant
open PersistentFailureFlag LowStateHorizon ExponentialMesh

theorem source_coupling_rate_jb247 : ∃ κ₀ : ℝ, 0 < κ₀ ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ d : ℝ, 0 < d → ∃ w₀ : ℝ, 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell B : ℝ, ∀ start : Node, ∀ hs : Valid start.side start.ratio,
      1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      0 < start.gap → start.ratio ≤ 23/10 → Consistent start → start.gap ≤ (23/10:ℝ)*B →
      let S := (Real.log B)^2
      let N := sourceHorizon S B
      (∀ n ≤ N,
        CouplingData.sourceLaw w ell S start hs (mesh κ w) n failed ≤
          ENNReal.ofReal (Real.exp (-(κ/2)*Real.sqrt (Real.log w))) ∧
        ∀ᵐ q ∂CouplingData.sourceLaw w ell S start hs (mesh κ w) n,
          q.2 = false → GoodAt (Real.log start.gap) (mesh κ w) n q.1) ∧
      (∀ᵐ q ∂CouplingData.sourceLaw w ell S start hs (mesh κ w) N,
        q.2 = false → q.1 = (none,CemeteryKernel.dead)) := by
  sorry

end NumberTheoryLean.SourceCouplingRate

end

end Erdos970

end OAI
end

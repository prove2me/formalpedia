-- Prove2me | Theorems.Thm_OAI_Erdos970_Erdos970Dependency_MarkedVisits_moving_canonical_missing_visit_jb247
-- name    : OAI.Erdos970.Erdos970Dependency.MarkedVisits.moving_canonical_missing_visit_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:54:21.769939+00:00
-- url     : https://prove2.me/theorems/d0c6e2fd-b71f-4cdb-93cf-c4b6edc88dd0
-- title:
--   OAI.Erdos970.Erdos970Dependency.MarkedVisits.moving_canonical_missing_visit_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.Erdos970Dependency.MarkedVisits.moving_canonical_missing_visit` of [lean/OAI/NumberTheory/Jacobsthal/Paths/CanonicalUniformMissingVisit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Paths/CanonicalUniformMissingVisit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.Erdos970Dependency.MarkedVisits`, with `open Filter Set MeasureTheory ProbabilityTheory`, `open scoped ProbabilityTheory ENNReal Topology`, `open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels`):
--
--   ```lean
--   theorem moving_canonical_missing_visit_jb247 {eps : ℝ} (heps : 0 < eps) :
--       ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K →
--         ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r → ∀ s : EvenState,
--           199/100 ≤ s.1 → s.1 ≤ 23/10 → ∀ N : ℕ,
--           finitePathMeasure (Sum.inl s) N
--             (closedNoHitEvent 1 N r (K*(Real.log w)^2) (rho*K*(Real.log w)^2) 1) ≤ ENNReal.ofReal eps
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.NumberTheoryLean.FinitePathMeasures.CostState`, `OAI.Erdos970.NumberTheoryLean.FinitePathMeasures.State`, `OAI.Erdos970.NumberTheoryLean.TransitionKernels.EvenState` and `OAI.Erdos970.NumberTheoryLean.TransitionKernels.OddState` (definitions bundle `OAIQ247J001` of this split); `OAI.Erdos970.Erdos970Dependency.MarkedVisits.closedNoHitEvent` and `OAI.Erdos970.NumberTheoryLean.FinitePathMeasures.finitePathMeasure` (definitions bundle `OAIQ247J007` of this split).
--
--   **Used by.** The proof of `OAI.Erdos970.NumberTheoryLean.MovingPrimeWindowProbability.source_missing_window_probability_jb247` of this split imports it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Paths/CanonicalUniformMissingVisit.lean (declaration OAI.Erdos970.Erdos970Dependency.MarkedVisits.moving_canonical_missing_visit)

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Definitions.Def_OAIQ247J007

section

attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels

theorem moving_canonical_missing_visit_jb247 {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K →
      ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r → ∀ s : EvenState,
        199/100 ≤ s.1 → s.1 ≤ 23/10 → ∀ N : ℕ,
        finitePathMeasure (Sum.inl s) N
          (closedNoHitEvent 1 N r (K*(Real.log w)^2) (rho*K*(Real.log w)^2) 1) ≤ ENNReal.ofReal eps := by
  sorry

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

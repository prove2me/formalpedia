-- Prove2me | Theorems.Thm_OAI_Invariant233_ProductScaleLaws_eventually_source_product_tail_estimate
-- name    : OAI.Invariant233.ProductScaleLaws.eventually_source_product_tail_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:33:43.259261+00:00
-- url     : https://prove2.me/theorems/ba0ab3f6-cf8e-49cd-9cf5-c5229a0a7e03
-- title:
--   OAI.Invariant233.ProductScaleLaws.eventually_source_product_tail_estimate: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.ProductScaleLaws.eventually_source_product_tail_estimate` of [lean/OAI/Analysis/IrrationalRotation/Product/SourceProductTailRealization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Product/SourceProductTailRealization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.ProductScaleLaws`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped BigOperators Topology`, `open OrderedProductCoupling`):
--
--   ```lean
--   theorem eventually_source_product_tail_estimate
--       (e : ℕ ≃ Σ s, Fin (p.m s))
--       (he : ∀ a : Σ s, Fin (p.m s),
--         e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
--       (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
--       (hb : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
--         θ i ∈ Icc (1 / p.N j) (2 / p.N j))
--       (hsmall : ∀ s, ProductPhases.smallPhaseCondition
--         (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
--       (hlarge : ∀ᶠ s in atTop, ProductPhases.largePhaseCondition
--         (ProductPhases.consecutiveBlock p.m s) (p.N s) θ) :
--       ∀ᶠ j in atTop, SourceTailEstimate p e θ j
--         (sourceBlocks p.m p.a p.b hp.m_ge_100
--           (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
--           (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.ProductScaleData`, `OAI.Invariant233.ProductScaleData.a` and `OAI.Invariant233.ProductScaleData.b` (definitions bundle `Q234IR000` of this split); `OAI.Invariant233.ProductPhases.consecutiveBlock`, `OAI.Invariant233.ProductPhases.largePhaseCondition` and `OAI.Invariant233.ProductPhases.smallPhaseCondition` (definitions bundle `Q234IR001` of this split); `OAI.Invariant233.ProductScaleLaws`, `OAI.Invariant233.OrderedProductCoupling.SourceTailEstimate`, `OAI.Invariant233.OrderedProductCoupling.sourceBlocks`, `OAI.Invariant233.ProductScaleData.N`, `OAI.Invariant233.ProductScaleLaws.a_bounds` and `OAI.Invariant233.ProductScaleLaws.b_bounds` (definitions bundle `Q234IR003` of this split).
--
--   **Used by.** The proof of `OAI.Invariant233.ProductModel.hasOnlyTrivialInvariantProjections_of_sampling_and_phases` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Product/SourceProductTailRealization.lean (declaration OAI.Invariant233.ProductScaleLaws.eventually_source_product_tail_estimate)

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Find
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_Q234IR003

section

attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace Invariant233.ProductScaleLaws
open OrderedProductCoupling
variable {p : ProductScaleData} (hp : ProductScaleLaws p)

theorem eventually_source_product_tail_estimate
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (hb : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ∈ Icc (1 / p.N j) (2 / p.N j))
    (hsmall : ∀ s, ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ᶠ s in atTop, ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ) :
    ∀ᶠ j in atTop, SourceTailEstimate p e θ j
      (sourceBlocks p.m p.a p.b hp.m_ge_100
        (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
        (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j) := by
  sorry

end Invariant233.ProductScaleLaws

end

end OAI
end

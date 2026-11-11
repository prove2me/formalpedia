-- Prove2me | Theorems.Thm_OAI_Invariant233_BlockedProductCoupling_eventually_flatSourceEvent_mass
-- name    : OAI.Invariant233.BlockedProductCoupling.eventually_flatSourceEvent_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:31:00.042214+00:00
-- url     : https://prove2.me/theorems/d328a159-960a-4b14-b121-779afecd5b21
-- title:
--   OAI.Invariant233.BlockedProductCoupling.eventually_flatSourceEvent_mass: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.BlockedProductCoupling.eventually_flatSourceEvent_mass` of [lean/OAI/Analysis/IrrationalRotation/Analysis/BlockedSourceTransport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Analysis/BlockedSourceTransport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.BlockedProductCoupling`, with `open scoped BigOperators`, `open MeasureTheory Set Filter`):
--
--   ```lean
--   theorem eventually_flatSourceEvent_mass {p : ProductScaleData} (hp : ProductScaleLaws p)
--       (e : ℕ ≃ Σ s, Fin (p.m s)) {r : ProductModel.Base → ℝ} (hr : Measurable r)
--       (hi : ∀ᵐ x ∂ProductModel.baseMeasure, 0 < r x ∧ r x < 1) :
--       ∀ᶠ j in atTop, Real.exp (-82) / 2 ≤
--         (OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
--           hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
--           (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j)).real
--           (flatSourceEvent p e r j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.ProductScaleData`, `OAI.Invariant233.BlockedProductCoupling.flatSourceEvent`, `OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace`, `OAI.Invariant233.OrderedProductCoupling.CoordinateSample`, `OAI.Invariant233.OrderedProductCoupling.Sample`, `OAI.Invariant233.ProductScaleData.a` and `OAI.Invariant233.ProductScaleData.b` (definitions bundle `Q234IR000` of this split); `OAI.Invariant233.ProductScaleLaws`, `OAI.Invariant233.OrderedProductCoupling.law`, `OAI.Invariant233.OrderedProductCoupling.sourceBlocks`, `OAI.Invariant233.ProductScaleLaws.a_bounds` and `OAI.Invariant233.ProductScaleLaws.b_bounds` (definitions bundle `Q234IR003` of this split); `OAI.Invariant233.Circle`, `OAI.Invariant233.ProductModel.Base` and `OAI.Invariant233.ProductModel.baseMeasure` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.ProductModel.eventually_actualSource_conditionalData` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Analysis/BlockedSourceTransport.lean (declaration OAI.Invariant233.BlockedProductCoupling.eventually_flatSourceEvent_mass)

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

section

attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

noncomputable section
open MeasureTheory Set Filter

namespace Invariant233.BlockedProductCoupling

theorem eventually_flatSourceEvent_mass {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s)) {r : ProductModel.Base → ℝ} (hr : Measurable r)
    (hi : ∀ᵐ x ∂ProductModel.baseMeasure, 0 < r x ∧ r x < 1) :
    ∀ᶠ j in atTop, Real.exp (-82) / 2 ≤
      (OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
        hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
        (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j)).real
        (flatSourceEvent p e r j) := by
  sorry

end Invariant233.BlockedProductCoupling

end

end OAI
end

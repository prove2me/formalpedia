-- Prove2me | Theorems.Thm_OAI_Invariant233_ProductModel_eventually_actualSource_conditionalData
-- name    : OAI.Invariant233.ProductModel.eventually_actualSource_conditionalData
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:32:07.51921+00:00
-- url     : https://prove2.me/theorems/c278eb82-b0d7-4c05-b01f-5b0966c4422f
-- title:
--   OAI.Invariant233.ProductModel.eventually_actualSource_conditionalData: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.ProductModel.eventually_actualSource_conditionalData` of [lean/OAI/Analysis/IrrationalRotation/Couplings/ProductSourceConditionalData.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Couplings/ProductSourceConditionalData.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.ProductModel`, with `open MeasureTheory Filter`, `open scoped ENNReal Topology`, `open OrderedProductCoupling`, `open InvariantProjection.ConditionalConvolution`):
--
--   ```lean
--   theorem eventually_actualSource_conditionalData
--       {p : ProductScaleData} (hp : ProductScaleLaws p)
--       (e : ℕ ≃ Σ s, Fin (p.m s))
--       (he : ∀ a : Σ s, Fin (p.m s),
--         e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
--       (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
--       (hphase : ∀ i, θ i ∈ Set.Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
--       (A : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
--       (hF : IsCovariantFieldRepresentation θ A F 1)
--       (hproj : ∀ x, IsStarProjection (F x))
--       (hinv : (1 - A) * weightedOperator θ (fun i => p.C (e i).1) * A = 0)
--       (hdiag : ∀ᵐ x ∂baseMeasure,
--         0 < BlockedProductCoupling.projectionDiagonal F x ∧
--         BlockedProductCoupling.projectionDiagonal F x < 1)
--       (hpair : ∀ j, ∀ᵐ xy ∂circlePairLaw (actualSourceParameters hp e j),
--         PairIdentity θ (fun i => p.C (e i).1) F xy)
--       (htail : ∀ᶠ j in atTop,
--         SourceTailEstimate p e θ j (actualSourceParameters hp e j)) :
--       ∀ᶠ j in atTop,
--         Nonempty (Data Sample (law (actualSourceParameters hp e j))
--           (p.K j) (p.coefficientBound j) (1 / ((j + 1 : ℕ) : ℝ))
--           (Real.exp (-82) / 2) (Real.exp (-p.L j)) (Real.exp (-p.L j / 400)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.ProductScaleData`, `OAI.Invariant233.BlockedProductCoupling.projectionDiagonal`, `OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace`, `OAI.Invariant233.OrderedProductCoupling.CoordinateSample` and `OAI.Invariant233.OrderedProductCoupling.Sample` (definitions bundle `Q234IR000` of this split); `OAI.InvariantProjection.ConditionalConvolution.Data` (definitions bundle `Q234IR001` of this split); `OAI.Invariant233.ProductScaleLaws`, `OAI.Invariant233.OrderedProductCoupling.SourceTailEstimate`, `OAI.Invariant233.OrderedProductCoupling.circlePairLaw`, `OAI.Invariant233.OrderedProductCoupling.law`, `OAI.Invariant233.ProductModel.PairIdentity`, `OAI.Invariant233.ProductModel.actualSourceParameters`, `OAI.Invariant233.ProductScaleData.N` and `OAI.Invariant233.ProductScaleData.coefficientBound` (definitions bundle `Q234IR003` of this split); `OAI.Invariant233.Circle`, `OAI.Invariant233.ProductModel.Base`, `OAI.Invariant233.ProductModel.EndpointPair`, `OAI.Invariant233.ProductModel.Fiber`, `OAI.Invariant233.ProductModel.Hilbert`, `OAI.Invariant233.ProductModel.IsCovariantFieldRepresentation`, `OAI.Invariant233.ProductModel.baseMeasure`, `OAI.Invariant233.ProductModel.instAddCommMonoidProductWeightedOperator`, `OAI.Invariant233.ProductModel.instModuleProductWeightedOperator`, `OAI.Invariant233.ProductModel.instTopologicalSpaceProductWeightedOperator` and `OAI.Invariant233.ProductModel.weightedOperator` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.ProductModel.hasOnlyTrivialInvariantProjections_of_sampling_and_phases` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Couplings/ProductSourceConditionalData.lean (declaration OAI.Invariant233.ProductModel.eventually_actualSource_conditionalData)

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Find
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
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
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

section

attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductModel
open OrderedProductCoupling
open InvariantProjection.ConditionalConvolution

theorem eventually_actualSource_conditionalData
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (hphase : ∀ i, θ i ∈ Set.Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
    (A : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : IsCovariantFieldRepresentation θ A F 1)
    (hproj : ∀ x, IsStarProjection (F x))
    (hinv : (1 - A) * weightedOperator θ (fun i => p.C (e i).1) * A = 0)
    (hdiag : ∀ᵐ x ∂baseMeasure,
      0 < BlockedProductCoupling.projectionDiagonal F x ∧
      BlockedProductCoupling.projectionDiagonal F x < 1)
    (hpair : ∀ j, ∀ᵐ xy ∂circlePairLaw (actualSourceParameters hp e j),
      PairIdentity θ (fun i => p.C (e i).1) F xy)
    (htail : ∀ᶠ j in atTop,
      SourceTailEstimate p e θ j (actualSourceParameters hp e j)) :
    ∀ᶠ j in atTop,
      Nonempty (Data Sample (law (actualSourceParameters hp e j))
        (p.K j) (p.coefficientBound j) (1 / ((j + 1 : ℕ) : ℝ))
        (Real.exp (-82) / 2) (Real.exp (-p.L j)) (Real.exp (-p.L j / 400))) := by
  sorry

end Invariant233.ProductModel

end

end OAI
end

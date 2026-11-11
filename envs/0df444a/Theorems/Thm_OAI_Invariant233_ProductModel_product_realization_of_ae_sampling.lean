-- Prove2me | Theorems.Thm_OAI_Invariant233_ProductModel_product_realization_of_ae_sampling
-- name    : OAI.Invariant233.ProductModel.product_realization_of_ae_sampling
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:32:00.237163+00:00
-- url     : https://prove2.me/theorems/6484a9a2-e474-4e82-b7ed-b3d914abaad0
-- title:
--   OAI.Invariant233.ProductModel.product_realization_of_ae_sampling: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.ProductModel.product_realization_of_ae_sampling` of [lean/OAI/Analysis/IrrationalRotation/Product/ProductRealizationAssembly.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Product/ProductRealizationAssembly.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.ProductModel`, with `open MeasureTheory Filter Set`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem product_realization_of_ae_sampling
--       (hsampling : ∀ (p : ProductScaleData) (_hp : ProductScaleLaws p)
--         (S : ℕ → ℝ) (_hS : ∀ i, 0 < S i)
--         (_hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
--           S i = (p.m j : ℝ) * p.K j),
--         ∀ᵐ θ ∂Measure.infinitePi (fun i =>
--           ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))),
--           HasAllFiniteCoordinateSampling θ) :
--       ∃ θ c : ℕ → ℝ, AdmissibleAnglesAndCosts θ c ∧
--         HasAllFiniteCoordinateSampling θ ∧
--         (∀ᵐ x ∂baseMeasure, 0 < weight θ c x) ∧
--         HasNegInfiniteLogIntegral baseMeasure (weight θ c) ∧
--         IsTypeII1FactorWithVector (factor θ) traceVector ∧
--         HasSeparablePredual (factor θ) ∧
--         weightedOperator θ c ∈ factor θ ∧ weightedOperator θ c ≠ 0 ∧
--         NormQuasinilpotent (weightedOperator θ c) ∧
--         vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) = 0 ∧
--         spectrum ℂ (weightedOperator θ c) = {0} ∧
--         IsVectorBrownMeasure traceVector (weightedOperator θ c) (Measure.dirac 0) ∧
--         HasOnlyTrivialInvariantProjections (factor θ) (weightedOperator θ c) ∧
--         ProductPolarStructure shiftOperator (weightedOperator θ c)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.ProductScaleData` (definitions bundle `Q234IR000` of this split); `OAI.Invariant233.ProductPhases.consecutiveBlock` (definitions bundle `Q234IR001` of this split); `OAI.Invariant233.ProductScaleLaws` (definitions bundle `Q234IR003` of this split); `OAI.Invariant233.Circle`, `OAI.Invariant233.HasNegInfiniteLogIntegral`, `OAI.Invariant233.HasOnlyTrivialInvariantProjections`, `OAI.Invariant233.HasSeparablePredual`, `OAI.Invariant233.IsTypeII1FactorWithVector`, `OAI.Invariant233.IsVectorBrownMeasure`, `OAI.Invariant233.NormQuasinilpotent`, `OAI.Invariant233.ProductPolarStructure`, `OAI.Invariant233.vectorFugledeKadisonDeterminant`, `OAI.Invariant233.ProductModel.AdmissibleAnglesAndCosts`, `OAI.Invariant233.ProductModel.Base`, `OAI.Invariant233.ProductModel.Fiber`, `OAI.Invariant233.ProductModel.HasAllFiniteCoordinateSampling`, `OAI.Invariant233.ProductModel.Hilbert`, `OAI.Invariant233.ProductModel.baseMeasure`, `OAI.Invariant233.ProductModel.factor`, `OAI.Invariant233.ProductModel.instAddCommMonoidProductWeightedOperator`, `OAI.Invariant233.ProductModel.instModuleProductWeightedOperator`, `OAI.Invariant233.ProductModel.instTopologicalSpaceProductWeightedOperator`, `OAI.Invariant233.ProductModel.shiftOperator`, `OAI.Invariant233.ProductModel.traceVector`, `OAI.Invariant233.ProductModel.weight` and `OAI.Invariant233.ProductModel.weightedOperator` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.Results.product_realization` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Product/ProductRealizationAssembly.lean (declaration OAI.Invariant233.ProductModel.product_realization_of_ae_sampling)

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Countable
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
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
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
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
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Sequences
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

section

attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Invariant233.ProductModel

theorem product_realization_of_ae_sampling
    (hsampling : ∀ (p : ProductScaleData) (_hp : ProductScaleLaws p)
      (S : ℕ → ℝ) (_hS : ∀ i, 0 < S i)
      (_hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
        S i = (p.m j : ℝ) * p.K j),
      ∀ᵐ θ ∂Measure.infinitePi (fun i =>
        ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))),
        HasAllFiniteCoordinateSampling θ) :
    ∃ θ c : ℕ → ℝ, AdmissibleAnglesAndCosts θ c ∧
      HasAllFiniteCoordinateSampling θ ∧
      (∀ᵐ x ∂baseMeasure, 0 < weight θ c x) ∧
      HasNegInfiniteLogIntegral baseMeasure (weight θ c) ∧
      IsTypeII1FactorWithVector (factor θ) traceVector ∧
      HasSeparablePredual (factor θ) ∧
      weightedOperator θ c ∈ factor θ ∧ weightedOperator θ c ≠ 0 ∧
      NormQuasinilpotent (weightedOperator θ c) ∧
      vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) = 0 ∧
      spectrum ℂ (weightedOperator θ c) = {0} ∧
      IsVectorBrownMeasure traceVector (weightedOperator θ c) (Measure.dirac 0) ∧
      HasOnlyTrivialInvariantProjections (factor θ) (weightedOperator θ c) ∧
      ProductPolarStructure shiftOperator (weightedOperator θ c) := by
  sorry

end Invariant233.ProductModel

end

end OAI
end

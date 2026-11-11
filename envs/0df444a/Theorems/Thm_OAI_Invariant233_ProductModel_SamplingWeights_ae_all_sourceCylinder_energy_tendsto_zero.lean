-- Prove2me | Theorems.Thm_OAI_Invariant233_ProductModel_SamplingWeights_ae_all_sourceCylinder_energy_tendsto_zero
-- name    : OAI.Invariant233.ProductModel.SamplingWeights.ae_all_sourceCylinder_energy_tendsto_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:31:22.986661+00:00
-- url     : https://prove2.me/theorems/352dabeb-96cb-4b62-b25c-6c26d1a20bcd
-- title:
--   OAI.Invariant233.ProductModel.SamplingWeights.ae_all_sourceCylinder_energy_tendsto_zero: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.ProductModel.SamplingWeights.ae_all_sourceCylinder_energy_tendsto_zero` of [lean/OAI/Analysis/IrrationalRotation/Sampling/ProductSourceSamplingEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Sampling/ProductSourceSamplingEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.ProductModel.SamplingWeights`, with `open MeasureTheory Filter Set`, `open scoped ENNReal Topology`, `open SamplingCylinderWeak`):
--
--   ```lean
--   theorem ae_all_sourceCylinder_energy_tendsto_zero
--       {p : ProductScaleData} (hp : ProductScaleLaws p)
--       (N : ℕ → Finset ℕ) (hN : ∀ᶠ j in atTop, ProductSamplingPowersAt p j (N j))
--       (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
--       (hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
--         S i = (p.m j : ℝ) * p.K j) :
--       ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
--         (Icc (1 / S i) (2 / S i))),
--         ∀ (I : Finset ℕ) (t : CylinderTest (Bool × ℕ)),
--         Tendsto (fun j => ∫ x,
--           (sourceTestedError p N false I (cylinderCoordinateSet t false)
--             (cylinderCoordinateSet t true) j θ x)^2 ∂baseMeasure) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.ProductScaleData` (definitions bundle `Q234IR000` of this split); `OAI.Invariant233.ProductPhases.consecutiveBlock`, `OAI.Invariant233.SamplingCylinderWeak.CylinderTest` and `OAI.Invariant233.ProductModel.SamplingWeights.cylinderCoordinateSet` (definitions bundle `Q234IR001` of this split); `OAI.Invariant233.ProductSamplingPowersAt`, `OAI.Invariant233.ProductScaleLaws` and `OAI.Invariant233.ProductModel.SamplingWeights.sourceTestedError` (definitions bundle `Q234IR003` of this split); `OAI.Invariant233.Circle`, `OAI.Invariant233.ProductModel.Base` and `OAI.Invariant233.ProductModel.baseMeasure` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.Results.product_realization` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Sampling/ProductSourceSamplingEnergy.lean (declaration OAI.Invariant233.ProductModel.SamplingWeights.ae_all_sourceCylinder_energy_tendsto_zero)

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

section

attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.ProductModel.SamplingWeights
open SamplingCylinderWeak

theorem ae_all_sourceCylinder_energy_tendsto_zero
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (hN : ∀ᶠ j in atTop, ProductSamplingPowersAt p j (N j))
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      S i = (p.m j : ℝ) * p.K j) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Icc (1 / S i) (2 / S i))),
      ∀ (I : Finset ℕ) (t : CylinderTest (Bool × ℕ)),
      Tendsto (fun j => ∫ x,
        (sourceTestedError p N false I (cylinderCoordinateSet t false)
          (cylinderCoordinateSet t true) j θ x)^2 ∂baseMeasure) atTop (𝓝 0) := by
  sorry

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

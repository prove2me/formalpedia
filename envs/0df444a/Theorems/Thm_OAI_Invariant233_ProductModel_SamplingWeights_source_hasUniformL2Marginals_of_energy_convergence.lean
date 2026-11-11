-- Prove2me | Theorems.Thm_OAI_Invariant233_ProductModel_SamplingWeights_source_hasUniformL2Marginals_of_energy_convergence
-- name    : OAI.Invariant233.ProductModel.SamplingWeights.source_hasUniformL2Marginals_of_energy_convergence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:33:07.696203+00:00
-- url     : https://prove2.me/theorems/41f187b0-b830-4087-ad6c-5af0c7665b2f
-- title:
--   OAI.Invariant233.ProductModel.SamplingWeights.source_hasUniformL2Marginals_of_energy_convergence: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.ProductModel.SamplingWeights.source_hasUniformL2Marginals_of_energy_convergence` of [lean/OAI/Analysis/IrrationalRotation/Sampling/ProductSourceSamplingL2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Sampling/ProductSourceSamplingL2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.ProductModel.SamplingWeights`, with `open MeasureTheory Filter Set`, `open scoped ENNReal BigOperators Topology`):
--
--   ```lean
--   theorem source_hasUniformL2Marginals_of_energy_convergence
--       {p : ProductScaleData} (hp : ProductScaleLaws p) (N : ℕ → Finset ℕ)
--       (θ : ℕ → ℝ) (I : Finset ℕ)
--       (herr : ∀ endpoint : Bool, Tendsto (fun j => ∫ x,
--         (sourceTestedError p N endpoint I (fun _ => univ) (fun _ => univ) j θ x)^2
--           ∂baseMeasure) atTop (𝓝 0)) :
--       HasUniformL2Marginals (fun j => TailTrimming.orbitAverageMeasure θ (N j)
--         (fun n x => ENNReal.ofReal (orbitWeight (Finset.range (p.prefixCount (j + 1))) I
--           ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2) θ n x)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.ProductScaleData` (definitions bundle `Q234IR000` of this split); `OAI.Invariant233.ProductModel.SamplingWeights.orbitWeight` and `OAI.Invariant233.ProductModel.TailTrimming.orbitAverageMeasure` (definitions bundle `Q234IR001` of this split); `OAI.Invariant233.ProductScaleLaws`, `OAI.Invariant233.ProductScaleData.prefixCount` and `OAI.Invariant233.ProductModel.SamplingWeights.sourceTestedError` (definitions bundle `Q234IR003` of this split); `OAI.Invariant233.Circle`, `OAI.Invariant233.ProductModel.Base`, `OAI.Invariant233.ProductModel.HasUniformL2Marginals` and `OAI.Invariant233.ProductModel.baseMeasure` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.Results.product_realization` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Sampling/ProductSourceSamplingL2.lean (declaration OAI.Invariant233.ProductModel.SamplingWeights.source_hasUniformL2Marginals_of_energy_convergence)

import Mathlib
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
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
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel.SamplingWeights

theorem source_hasUniformL2Marginals_of_energy_convergence
    {p : ProductScaleData} (hp : ProductScaleLaws p) (N : ℕ → Finset ℕ)
    (θ : ℕ → ℝ) (I : Finset ℕ)
    (herr : ∀ endpoint : Bool, Tendsto (fun j => ∫ x,
      (sourceTestedError p N endpoint I (fun _ => univ) (fun _ => univ) j θ x)^2
        ∂baseMeasure) atTop (𝓝 0)) :
    HasUniformL2Marginals (fun j => TailTrimming.orbitAverageMeasure θ (N j)
      (fun n x => ENNReal.ofReal (orbitWeight (Finset.range (p.prefixCount (j + 1))) I
        ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2) θ n x))) := by
  sorry

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_Invariant233_TrialSampling_expectation_squaredError_le_actual_bound
-- name    : OAI.Invariant233.TrialSampling.expectation_squaredError_le_actual_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:34:04.1072+00:00
-- url     : https://prove2.me/theorems/5592a2fc-e42a-43e7-ad8c-6797d56f4692
-- title:
--   OAI.Invariant233.TrialSampling.expectation_squaredError_le_actual_bound: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.TrialSampling.expectation_squaredError_le_actual_bound` of [lean/OAI/Analysis/IrrationalRotation/Sampling/TrialSamplingActualMoments.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Sampling/TrialSamplingActualMoments.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.TrialSampling`, with `open MeasureTheory Filter`, `open scoped ENNReal Topology BigOperators`):
--
--   ```lean
--   theorem expectation_squaredError_le_actual_bound
--       {m : ℕ} (hm : 200 ≤ m) {N : ℝ} (hN : 0 < N)
--       (hNm : N ≤ (m : ℝ) ^ 2) (samples : Finset ℕ) (hs : samples.Nonempty)
--       (hcard : (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (samples.card : ℝ))
--       (hrange : ∀ n ∈ samples, ScalarSampling.samplingHorizon m / 2 ≤ (n : ℝ))
--       (hpair : ∀ n ∈ samples, ∀ n' ∈ samples, n ≠ n' →
--         ScalarSampling.SamplingPair m N N n n') (endpoint : Bool) :
--       (∫⁻ phase, squaredError m samples endpoint phase ∂phaseLaw m N) ≤
--         ENNReal.ofReal (SamplingAsymptotics.meanSquareBound 3509 m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.SamplingAsymptotics.meanSquareBound`, `OAI.Invariant233.ScalarSampling.SamplingPair`, `OAI.Invariant233.ScalarSampling.samplingHorizon` and `OAI.Invariant233.TrialSampling.phaseLaw` (definitions bundle `Q234IR001` of this split); `OAI.Invariant233.TrialSampling.squaredError` (definitions bundle `Q234IR003` of this split).
--
--   **Used by.** The proof of `OAI.Invariant233.exists_circle_parameters` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Sampling/TrialSamplingActualMoments.lean (declaration OAI.Invariant233.TrialSampling.expectation_squaredError_le_actual_bound)

import Mathlib
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_Q234IR003

section

attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace Invariant233.TrialSampling

theorem expectation_squaredError_le_actual_bound
    {m : ℕ} (hm : 200 ≤ m) {N : ℝ} (hN : 0 < N)
    (hNm : N ≤ (m : ℝ) ^ 2) (samples : Finset ℕ) (hs : samples.Nonempty)
    (hcard : (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (samples.card : ℝ))
    (hrange : ∀ n ∈ samples, ScalarSampling.samplingHorizon m / 2 ≤ (n : ℝ))
    (hpair : ∀ n ∈ samples, ∀ n' ∈ samples, n ≠ n' →
      ScalarSampling.SamplingPair m N N n n') (endpoint : Bool) :
    (∫⁻ phase, squaredError m samples endpoint phase ∂phaseLaw m N) ≤
      ENNReal.ofReal (SamplingAsymptotics.meanSquareBound 3509 m) := by
  sorry

end Invariant233.TrialSampling

end

end OAI
end

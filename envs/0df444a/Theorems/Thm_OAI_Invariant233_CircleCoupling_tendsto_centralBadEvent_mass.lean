-- Prove2me | Theorems.Thm_OAI_Invariant233_CircleCoupling_tendsto_centralBadEvent_mass
-- name    : OAI.Invariant233.CircleCoupling.tendsto_centralBadEvent_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:23:26.033209+00:00
-- url     : https://prove2.me/theorems/63f169a3-cf9d-49a7-8eba-41a81d76b342
-- title:
--   OAI.Invariant233.CircleCoupling.tendsto_centralBadEvent_mass: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.CircleCoupling.tendsto_centralBadEvent_mass` of [lean/OAI/Analysis/IrrationalRotation/Rotation/CircleTruncationMass.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Rotation/CircleTruncationMass.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.CircleCoupling`, with `open MeasureTheory Filter Set`, `open scoped Topology`):
--
--   ```lean
--   theorem tendsto_centralBadEvent_mass
--       (hr : ∀ i, 0 < MixedRadix.radices p.q i) {r : Circle → ℝ}
--       (hrm : Measurable r) (hri : ∀ᵐ x ∂volume, 0 < r x ∧ r x < 1) :
--       Tendsto (fun j : ℕ => (law p j).real (centralBadEvent p j hr r))
--         atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.CircleParameterData`, `OAI.Invariant233.CircleParameterLaws`, `OAI.Invariant233.CircleCoupling.Sample`, `OAI.Invariant233.CircleCoupling.centralBadEvent`, `OAI.Invariant233.CircleCoupling.law`, `OAI.Invariant233.CircleDigitCoupling.CoordinateSample`, `OAI.Invariant233.CircleDigitCoupling.Label`, `OAI.Invariant233.MixedRadix.radices` and `OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace` (definitions bundle `Q234IR000` of this split); `OAI.Invariant233.Circle` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field_with_truncation_mass` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Rotation/CircleTruncationMass.lean (declaration OAI.Invariant233.CircleCoupling.tendsto_centralBadEvent_mass)

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR000

section

attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Invariant233.CircleCoupling

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem tendsto_centralBadEvent_mass
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) {r : Circle → ℝ}
    (hrm : Measurable r) (hri : ∀ᵐ x ∂volume, 0 < r x ∧ r x < 1) :
    Tendsto (fun j : ℕ => (law p j).real (centralBadEvent p j hr r))
      atTop (𝓝 0) := by
  sorry

end Invariant233.CircleCoupling

end

end OAI
end

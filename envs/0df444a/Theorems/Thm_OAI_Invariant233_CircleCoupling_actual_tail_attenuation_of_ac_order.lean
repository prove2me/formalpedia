-- Prove2me | Theorems.Thm_OAI_Invariant233_CircleCoupling_actual_tail_attenuation_of_ac_order
-- name    : OAI.Invariant233.CircleCoupling.actual_tail_attenuation_of_ac_order
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:23:56.920198+00:00
-- url     : https://prove2.me/theorems/71c53658-fd28-4b5b-830f-71813e9f4841
-- title:
--   OAI.Invariant233.CircleCoupling.actual_tail_attenuation_of_ac_order: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.CircleCoupling.actual_tail_attenuation_of_ac_order` of [lean/OAI/Analysis/IrrationalRotation/Couplings/CircleCouplingAttenuation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Couplings/CircleCouplingAttenuation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.CircleCoupling`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped ENNReal`, `open CircleDigitCoupling CircleParameterData CouplingMarginalBounds`):
--
--   ```lean
--   lemma actual_tail_attenuation_of_ac_order (j : ℕ) (hj : 1 ≤ j)
--       (hr : ∀ i, 0 < MixedRadix.radices p.q i)
--       (hac : ∀ side, (law p j).map (point p hr side) ≪ circleMeasure)
--       (horder : ∀ᵐ ω ∂law p j, ∀ i : p.Coord,
--         p.coordinate i.2 (point p hr false ω) ≤ p.coordinate i.2 (point p hr true ω)) :
--       TailAttenuation θ p j hr
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.CircleParameterData`, `OAI.Invariant233.CircleParameterLaws`, `OAI.Invariant233.CircleCoupling.Sample`, `OAI.Invariant233.CircleCoupling.TailAttenuation`, `OAI.Invariant233.CircleCoupling.law`, `OAI.Invariant233.CircleCoupling.point`, `OAI.Invariant233.CircleDigitCoupling.CoordinateSample`, `OAI.Invariant233.CircleDigitCoupling.Label`, `OAI.Invariant233.CircleParameterData.Coord`, `OAI.Invariant233.CircleParameterData.block`, `OAI.Invariant233.CircleParameterData.coordinate`, `OAI.Invariant233.MixedRadix.radices` and `OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace` (definitions bundle `Q234IR000` of this split); `OAI.Invariant233.Circle` and `OAI.Invariant233.circleMeasure` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.CircleCoupling.tail_exceptional_families_of_subset` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Couplings/CircleCouplingAttenuation.lean (declaration OAI.Invariant233.CircleCoupling.actual_tail_attenuation_of_ac_order)

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData CouplingMarginalBounds
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma actual_tail_attenuation_of_ac_order (j : ℕ) (hj : 1 ≤ j)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (hac : ∀ side, (law p j).map (point p hr side) ≪ circleMeasure)
    (horder : ∀ᵐ ω ∂law p j, ∀ i : p.Coord,
      p.coordinate i.2 (point p hr false ω) ≤ p.coordinate i.2 (point p hr true ω)) :
    TailAttenuation θ p j hr := by
  sorry

end Invariant233.CircleCoupling

end

end OAI
end

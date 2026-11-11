-- Prove2me | Theorems.Thm_OAI_Invariant233_CircleParameterLaws_exists_rational_graph_field_with_truncation_mass
-- name    : OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field_with_truncation_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:03.895058+00:00
-- url     : https://prove2.me/theorems/53b3df82-3b2b-4f7e-9fdb-ebe09a4b8e24
-- title:
--   OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field_with_truncation_mass: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field_with_truncation_mass` of [lean/OAI/Analysis/IrrationalRotation/Operators/ProjectionTruncationMass.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Operators/ProjectionTruncationMass.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.CircleParameterLaws`, with `open MeasureTheory`, `open scoped ENNReal InnerProductSpace`):
--
--   ```lean
--   theorem exists_rational_graph_field_with_truncation_mass (hθ : Irrational θ)
--       (hr : ∀ i, 0 < MixedRadix.radices p.q i)
--       {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
--       (hPm : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
--       (hinv : (1 - P) * p.measurableOperator θ hp * P = 0)
--       (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
--       ∃ F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber,
--         (∀ x, IsStarProjection (F x)) ∧
--         (∀ x, ‖F x‖ ≤ ‖P‖) ∧
--         (∀ v, StronglyMeasurable fun x => F x v) ∧
--         (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
--         p.RationalGraphIdentities θ F ∧
--         ∃ J : ℕ, 1 ≤ J ∧ ∀ j : ℕ, J ≤ j →
--           Real.exp (-90) / 2 ≤ (CircleCoupling.law p j).real
--             (CircleCoupling.truncationEvent p j hr
--               (fun x => (inner ℂ e₀ (F x e₀)).re))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.CircleParameterData`, `OAI.Invariant233.CircleParameterLaws`, `OAI.Invariant233.CircleCoupling.Sample`, `OAI.Invariant233.CircleCoupling.law`, `OAI.Invariant233.CircleCoupling.truncationEvent`, `OAI.Invariant233.CircleDigitCoupling.CoordinateSample`, `OAI.Invariant233.CircleDigitCoupling.Label`, `OAI.Invariant233.CircleParameterData.RationalGraphIdentities`, `OAI.Invariant233.CircleParameterData.measurableOperator`, `OAI.Invariant233.MixedRadix.radices` and `OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace` (definitions bundle `Q234IR000` of this split); `OAI.Invariant233.PositiveDiagonalModel.Fiber` and `OAI.Invariant233.PositiveDiagonalModel.e0` (definitions bundle `Q234IR001` of this split); `OAI.Invariant233.Circle`, `OAI.Invariant233.circleMeasure`, `OAI.Invariant233.Rotation.Fiber`, `OAI.Invariant233.Rotation.Hilbert` and `OAI.Invariant233.Rotation.algebra` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.CircleParameterLaws.measurableOperator_hasOnlyTrivialInvariantProjections` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Operators/ProjectionTruncationMass.lean (declaration OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field_with_truncation_mass)

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Continuity
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
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR000
import Definitions.Def_Q234IR001

section

attribute [-instance] _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
local notation "e₀" => PositiveDiagonalModel.e0

theorem exists_rational_graph_field_with_truncation_mass (hθ : Irrational θ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hPm : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ∃ F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber,
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      p.RationalGraphIdentities θ F ∧
      ∃ J : ℕ, 1 ≤ J ∧ ∀ j : ℕ, J ≤ j →
        Real.exp (-90) / 2 ≤ (CircleCoupling.law p j).real
          (CircleCoupling.truncationEvent p j hr
            (fun x => (inner ℂ e₀ (F x e₀)).re)) := by
  sorry

end Invariant233.CircleParameterLaws

end

end OAI
end

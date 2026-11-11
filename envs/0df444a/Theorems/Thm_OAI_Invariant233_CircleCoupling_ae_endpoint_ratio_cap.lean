-- Prove2me | Theorems.Thm_OAI_Invariant233_CircleCoupling_ae_endpoint_ratio_cap
-- name    : OAI.Invariant233.CircleCoupling.ae_endpoint_ratio_cap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:23:46.520163+00:00
-- url     : https://prove2.me/theorems/7ac04d55-d629-45b7-a7fc-86fe57e9a318
-- title:
--   OAI.Invariant233.CircleCoupling.ae_endpoint_ratio_cap: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.CircleCoupling.ae_endpoint_ratio_cap` of [lean/OAI/Analysis/IrrationalRotation/Couplings/CircleCouplingHybrid.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Couplings/CircleCouplingHybrid.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.CircleCoupling`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped ENNReal Topology`, `open CircleParameterData`):
--
--   ```lean
--   lemma ae_endpoint_ratio_cap (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
--       ∀ᵐ ω ∂law p j, ∀ k : ℤ,
--         0 < p.floorCocycle θ k (point p hr true ω) / p.floorCocycle θ k (point p hr false ω) ∧
--         p.floorCocycle θ k (point p hr true ω) / p.floorCocycle θ k (point p hr false ω) ≤ 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.CircleParameterData`, `OAI.Invariant233.CircleParameterLaws`, `OAI.Invariant233.CircleCoupling.Sample`, `OAI.Invariant233.CircleCoupling.law`, `OAI.Invariant233.CircleCoupling.point`, `OAI.Invariant233.CircleDigitCoupling.CoordinateSample`, `OAI.Invariant233.CircleDigitCoupling.Label`, `OAI.Invariant233.CircleParameterData.floorCocycle`, `OAI.Invariant233.MixedRadix.radices` and `OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace` (definitions bundle `Q234IR000` of this split).
--
--   **Used by.** The proofs of `OAI.Invariant233.CircleCoupling.ae_endpointPairLaw_ratio_cap` and `OAI.Invariant233.CircleCoupling.orderedCouplingIdentities_of_rational` of this split import it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Couplings/CircleCouplingHybrid.lean (declaration OAI.Invariant233.CircleCoupling.ae_endpoint_ratio_cap)

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Moments.Variance
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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_Q234IR000

section

attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Invariant233.CircleCoupling
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma ae_endpoint_ratio_cap (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    ∀ᵐ ω ∂law p j, ∀ k : ℤ,
      0 < p.floorCocycle θ k (point p hr true ω) / p.floorCocycle θ k (point p hr false ω) ∧
      p.floorCocycle θ k (point p hr true ω) / p.floorCocycle θ k (point p hr false ω) ≤ 1 := by
  sorry

end Invariant233.CircleCoupling

end

end OAI
end

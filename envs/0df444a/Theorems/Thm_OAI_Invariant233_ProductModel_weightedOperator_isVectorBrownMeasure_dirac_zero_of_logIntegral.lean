-- Prove2me | Theorems.Thm_OAI_Invariant233_ProductModel_weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral
-- name    : OAI.Invariant233.ProductModel.weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:20:12.777544+00:00
-- url     : https://prove2.me/theorems/65a29150-fb71-4666-a87b-ea88bfc120b5
-- title:
--   OAI.Invariant233.ProductModel.weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.ProductModel.weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral` of [lean/OAI/Analysis/IrrationalRotation/Spectral/ProductBrownMeasure.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Spectral/ProductBrownMeasure.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.ProductModel`, with `open MeasureTheory Set`):
--
--   ```lean
--   theorem weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral
--       (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
--       (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
--       (hlog : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
--       IsVectorBrownMeasure traceVector (weightedOperator θ c) (Measure.dirac 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.Circle`, `OAI.Invariant233.HasNegInfiniteLogIntegral`, `OAI.Invariant233.IsVectorBrownMeasure`, `OAI.Invariant233.ProductModel.Base`, `OAI.Invariant233.ProductModel.Fiber`, `OAI.Invariant233.ProductModel.Hilbert`, `OAI.Invariant233.ProductModel.baseMeasure`, `OAI.Invariant233.ProductModel.traceVector`, `OAI.Invariant233.ProductModel.weight` and `OAI.Invariant233.ProductModel.weightedOperator` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.ProductModel.product_realization_of_ae_sampling` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Spectral/ProductBrownMeasure.lean (declaration OAI.Invariant233.ProductModel.weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral)

import Mathlib
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Nat.Find
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Piecewise
import Definitions.Def_IrrationalRotation

section

attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductModel

theorem weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral
    (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hlog : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    IsVectorBrownMeasure traceVector (weightedOperator θ c) (Measure.dirac 0) := by
  sorry

end Invariant233.ProductModel

end

end OAI
end

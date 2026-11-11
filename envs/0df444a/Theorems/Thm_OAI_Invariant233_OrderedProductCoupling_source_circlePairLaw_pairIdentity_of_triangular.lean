-- Prove2me | Theorems.Thm_OAI_Invariant233_OrderedProductCoupling_source_circlePairLaw_pairIdentity_of_triangular
-- name    : OAI.Invariant233.OrderedProductCoupling.source_circlePairLaw_pairIdentity_of_triangular
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:31:18.344305+00:00
-- url     : https://prove2.me/theorems/113cddb7-5e18-4607-aa90-18b3988da0ca
-- title:
--   OAI.Invariant233.OrderedProductCoupling.source_circlePairLaw_pairIdentity_of_triangular: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.OrderedProductCoupling.source_circlePairLaw_pairIdentity_of_triangular` of [lean/OAI/Analysis/IrrationalRotation/Couplings/ProductBiasedIdentityFromTriangular.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Couplings/ProductBiasedIdentityFromTriangular.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.OrderedProductCoupling`, with `open MeasureTheory`, `open scoped BigOperators`):
--
--   ```lean
--   theorem source_circlePairLaw_pairIdentity_of_triangular
--       (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
--       (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
--       (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
--       (e : ℕ ≃ Σ s, Fin (m s))
--       (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
--       (hc : ∀ i, 0 ≤ c i)
--       (F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber)
--       (hF : ∀ x, IsStarProjection (F x))
--       (hFm : ∀ i : ℤ, Measurable (fun x => F x (lp.single 2 i 1)))
--       (htri : ∀ I : Finset ℕ, ∀ᵐ xy ∂ProductModel.triangularLaw I,
--         ProductModel.PairIdentity θ c F xy) :
--       ∀ tag : ℕ, ∀ᵐ xy ∂circlePairLaw
--         (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm ha ha' hb hb' e tag),
--         ProductModel.PairIdentity θ c F xy
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.OrderedProductCoupling.sourceKappa`, `OAI.Invariant233.OrderedProductCoupling.sourceKappa_le` and `OAI.Invariant233.OrderedProductCoupling.sourceKappa_nonneg` (definitions bundle `Q234IR001` of this split); `OAI.Invariant233.sequenceHilbertIntMeasurableSpace`, `OAI.Invariant233.OrderedProductCoupling.circlePairLaw`, `OAI.Invariant233.OrderedProductCoupling.ofBlocks` and `OAI.Invariant233.ProductModel.PairIdentity` (definitions bundle `Q234IR003` of this split); `OAI.Invariant233.Circle`, `OAI.Invariant233.ProductModel.Base`, `OAI.Invariant233.ProductModel.EndpointPair`, `OAI.Invariant233.ProductModel.Fiber` and `OAI.Invariant233.ProductModel.triangularLaw` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.ProductModel.hasOnlyTrivialInvariantProjections_of_sampling_and_phases` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Couplings/ProductBiasedIdentityFromTriangular.lean (declaration OAI.Invariant233.OrderedProductCoupling.source_circlePairLaw_pairIdentity_of_triangular)

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Monotone.Basic
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
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

section

attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.OrderedProductCoupling

theorem source_circlePairLaw_pairIdentity_of_triangular
    (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s))
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i)
    (F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber)
    (hF : ∀ x, IsStarProjection (F x))
    (hFm : ∀ i : ℤ, Measurable (fun x => F x (lp.single 2 i 1)))
    (htri : ∀ I : Finset ℕ, ∀ᵐ xy ∂ProductModel.triangularLaw I,
      ProductModel.PairIdentity θ c F xy) :
    ∀ tag : ℕ, ∀ᵐ xy ∂circlePairLaw
      (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm ha ha' hb hb' e tag),
      ProductModel.PairIdentity θ c F xy := by
  sorry

end Invariant233.OrderedProductCoupling

end

end OAI
end

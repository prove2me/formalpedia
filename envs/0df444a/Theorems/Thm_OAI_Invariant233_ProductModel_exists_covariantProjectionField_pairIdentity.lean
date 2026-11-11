-- Prove2me | Theorems.Thm_OAI_Invariant233_ProductModel_exists_covariantProjectionField_pairIdentity
-- name    : OAI.Invariant233.ProductModel.exists_covariantProjectionField_pairIdentity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:33:51.573926+00:00
-- url     : https://prove2.me/theorems/2455f444-6a4d-407d-a80b-0d0b78d7fd64
-- title:
--   OAI.Invariant233.ProductModel.exists_covariantProjectionField_pairIdentity: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.ProductModel.exists_covariantProjectionField_pairIdentity` of [lean/OAI/Analysis/IrrationalRotation/Couplings/ProductPairIdentity.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Couplings/ProductPairIdentity.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.ProductModel`, with `open MeasureTheory`):
--
--   ```lean
--   theorem exists_covariantProjectionField_pairIdentity
--       (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
--       (hc : ∀ i, 0 ≤ c i) (hsampling : HasAllFiniteCoordinateSampling θ)
--       (p : Hilbert →L[ℂ] Hilbert) (hpM : p ∈ factor θ) (hp : IsStarProjection p)
--       (hinv : (1 - p) * weightedOperator θ c * p = 0) :
--       ∃ F : Base → Fiber →L[ℂ] Fiber,
--         IsCovariantFieldRepresentation θ p F 1 ∧
--         (∀ x, IsStarProjection (F x)) ∧
--         ∀ I : Finset ℕ, ∀ᵐ xy ∂triangularLaw I, PairIdentity θ c F xy
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.ProductModel.PairIdentity` (definitions bundle `Q234IR003` of this split); `OAI.Invariant233.Circle`, `OAI.Invariant233.ProductModel.Base`, `OAI.Invariant233.ProductModel.EndpointPair`, `OAI.Invariant233.ProductModel.Fiber`, `OAI.Invariant233.ProductModel.HasAllFiniteCoordinateSampling`, `OAI.Invariant233.ProductModel.Hilbert`, `OAI.Invariant233.ProductModel.IsCovariantFieldRepresentation`, `OAI.Invariant233.ProductModel.baseMeasure`, `OAI.Invariant233.ProductModel.factor`, `OAI.Invariant233.ProductModel.instAddCommMonoidProductWeightedOperator`, `OAI.Invariant233.ProductModel.instModuleProductWeightedOperator`, `OAI.Invariant233.ProductModel.instTopologicalSpaceProductWeightedOperator`, `OAI.Invariant233.ProductModel.triangularLaw` and `OAI.Invariant233.ProductModel.weightedOperator` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.ProductModel.hasOnlyTrivialInvariantProjections_of_sampling_and_phases` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Couplings/ProductPairIdentity.lean (declaration OAI.Invariant233.ProductModel.exists_covariantProjectionField_pairIdentity)

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

section

attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel

theorem exists_covariantProjectionField_pairIdentity
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (hsampling : HasAllFiniteCoordinateSampling θ)
    (p : Hilbert →L[ℂ] Hilbert) (hpM : p ∈ factor θ) (hp : IsStarProjection p)
    (hinv : (1 - p) * weightedOperator θ c * p = 0) :
    ∃ F : Base → Fiber →L[ℂ] Fiber,
      IsCovariantFieldRepresentation θ p F 1 ∧
      (∀ x, IsStarProjection (F x)) ∧
      ∀ I : Finset ℕ, ∀ᵐ xy ∂triangularLaw I, PairIdentity θ c F xy := by
  sorry

end Invariant233.ProductModel

end

end OAI
end

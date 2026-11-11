-- Prove2me | Theorems.Thm_OAI_Invariant233_Rotation_exponentialTransfer_projection_transport
-- name    : OAI.Invariant233.Rotation.exponentialTransfer_projection_transport
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:24:52.354859+00:00
-- url     : https://prove2.me/theorems/f309cfa9-0db9-40a4-a352-0f5f1d3406a9
-- title:
--   OAI.Invariant233.Rotation.exponentialTransfer_projection_transport: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.Rotation.exponentialTransfer_projection_transport` of [lean/OAI/Analysis/IrrationalRotation/Rotation/RotationProjectionTransport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Rotation/RotationProjectionTransport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.Rotation`, with `open MeasureTheory`):
--
--   ```lean
--   theorem exponentialTransfer_projection_transport
--       (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b)
--       (A B p : Hilbert →L[ℂ] Hilbert) (hp : p ∈ algebra θ) (hpP : IsStarProjection p)
--       (hAp : (1 - p) * A * p = 0)
--       (hD : ∀ ξ : (exponentialTransfer θ b).domain,
--         A ξ.val ∈ (exponentialTransfer θ b).domain)
--       (hI : ∀ ξ : (exponentialTransfer θ b).domain,
--         exponentialTransfer θ b ⟨A ξ.val, hD ξ⟩ = B (exponentialTransfer θ b ξ)) :
--       let P := (InvariantRotation.AffiliatedTransport.transported
--         (exponentialTransfer θ b) p.range).starProjection
--       P ∈ algebra θ ∧ IsStarProjection P ∧ (1 - P) * B * P = 0 ∧
--         vectorTrace vacuum P = vectorTrace vacuum p
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.Rotation.exponentialTransfer`, `OAI.InvariantRotation.AffiliatedTransport.transported` and `OAI.InvariantRotation.AffiliatedTransport.transported_hasOrthogonalProjection` (definitions bundle `Q234IR001` of this split); `OAI.Invariant233.Circle`, `OAI.Invariant233.circleMeasure`, `OAI.Invariant233.vectorTrace`, `OAI.Invariant233.Rotation.Fiber`, `OAI.Invariant233.Rotation.Hilbert`, `OAI.Invariant233.Rotation.algebra` and `OAI.Invariant233.Rotation.vacuum` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Rotation/RotationProjectionTransport.lean (declaration OAI.Invariant233.Rotation.exponentialTransfer_projection_transport)

import Mathlib
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR001

section

attribute [-instance] _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233

namespace Rotation

theorem exponentialTransfer_projection_transport
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b)
    (A B p : Hilbert →L[ℂ] Hilbert) (hp : p ∈ algebra θ) (hpP : IsStarProjection p)
    (hAp : (1 - p) * A * p = 0)
    (hD : ∀ ξ : (exponentialTransfer θ b).domain,
      A ξ.val ∈ (exponentialTransfer θ b).domain)
    (hI : ∀ ξ : (exponentialTransfer θ b).domain,
      exponentialTransfer θ b ⟨A ξ.val, hD ξ⟩ = B (exponentialTransfer θ b ξ)) :
    let P := (InvariantRotation.AffiliatedTransport.transported
      (exponentialTransfer θ b) p.range).starProjection
    P ∈ algebra θ ∧ IsStarProjection P ∧ (1 - P) * B * P = 0 ∧
      vectorTrace vacuum P = vectorTrace vacuum p := by
  sorry

end Rotation
end Invariant233

end

end OAI
end

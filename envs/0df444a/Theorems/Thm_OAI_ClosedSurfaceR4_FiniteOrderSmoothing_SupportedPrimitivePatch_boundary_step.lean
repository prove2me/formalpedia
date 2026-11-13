-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SupportedPrimitivePatch_boundary_step
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch.boundary_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:45:02.778785+00:00
-- url     : https://prove2.me/theorems/7130708c-5c27-4dd0-a197-ea0bdf1a00de
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch.boundary_step: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch.boundary_step` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/PrimitivePatchBoundaryStep.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/PrimitivePatchBoundaryStep.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch`, with `open Set Filter Manifold Bundle`, `open scoped ContDiff Manifold Topology`, `open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame`):
--
--   ```lean
--   theorem boundary_step {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]
--       (d : SupportedPrimitivePatch A i e F amp phi D)
--       (c₀ : PhaseBoundaryCurve B) (hi : (i : M) = (c₀.index : M))
--       (he : ∀ x, e x = c₀.phase x)
--       (curves : ι → PhaseBoundaryCurve B)
--       (hpair : ∀ j k, j ≠ k → ((curves j).carrier ∩ (curves k).carrier).Finite)
--       (htriple : ∀ j k l, j ≠ k → j ≠ l → k ≠ l →
--         (curves j).carrier ∩ (curves k).carrier ∩ (curves l).carrier = ∅)
--       (hD : IsOpen D) (hDr : interior (closure D) = D) (hfront : c₀.carrier = frontier D)
--       (hEf : Disjoint (boundaryCrossingSet curves univ) (frontier D))
--       {g : SmoothMetric M} (data : MetricGoodPhaseData g F)
--       (hF : IsSmoothIsometricImmersion M g F) (n : PreferredNormal F)
--       (hgeom : FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) F n)
--       (hcurrent : ∀ p ∈ c₀.carrier, c₀.second F p ≠ 0 ∧
--         spaceCoordinates (n.vector p) ≠ -normalize (c₀.second F p))
--       (hfrontGeom : ∀ j p, p ∈ (curves j).carrier ∩ frontier D →
--         0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n.vector p) ∧
--         0 < c₀.crossing (curves j) F p)
--       (hfirst : ∀ j p, p ∈ boundaryCrossingSet curves univ ∩ D → p ∈ (curves j).carrier →
--         (fderiv ℝ (surfacePhaseTransition ((curves j).index : M) (curves j).phase
--           (i : M) e) ((curves j).coordinate p) dy).1 ≠ 0)
--       {P : Set SmallModes.Base} (hP : P.Finite)
--       (hlocal : ∀ p ∈ (⋃ j, d.curve (curves j)) \ P,
--         ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧ ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧
--           (∀ x ∈ (⋃ j, d.curve (curves j)) ∩ N, f x = 0) ∧ fderiv ℝ f p dy ≠ 0)
--       (h : SmoothMetric M)
--       (htarget : h.inner = g.inner + (fun p => (amp p)^2 • SmoothingAtlas.phaseDifferentialSquare phi p)) :
--       ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
--         ∃ N : PreferredNormal W, FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) W N
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.JetPolynomial.Base` and `OAI.ClosedSurfaceR4.NormalFrame.Vec` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PreferredNormal` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryCrossingSet`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.VelocityFrame.normalize`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.coordinate` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseDifferentialSquare` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch.curve` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.patchStepDualAdd` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.surfacePhaseTransition`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.FiniteBoundaryGeometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.crossing` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.second` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.realize_sequence` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/PrimitivePatchBoundaryStep.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch.boundary_step)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SupportedPrimitivePatch
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.patchStepDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.patchStepFiberSpace
local instance patchStepDualSmul_r514022_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {A : SmoothingAtlas M} {i : A.centers}
    {e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base}
    {F : M → Space} {amp phi : M → ℝ} {D : Set M}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.patchStepFiberNormed
local instance patchStepSectionNormed_r514022_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance patchStepSectionSpace_r514022_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem boundary_step {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]
    (d : SupportedPrimitivePatch A i e F amp phi D)
    (c₀ : PhaseBoundaryCurve B) (hi : (i : M) = (c₀.index : M))
    (he : ∀ x, e x = c₀.phase x)
    (curves : ι → PhaseBoundaryCurve B)
    (hpair : ∀ j k, j ≠ k → ((curves j).carrier ∩ (curves k).carrier).Finite)
    (htriple : ∀ j k l, j ≠ k → j ≠ l → k ≠ l →
      (curves j).carrier ∩ (curves k).carrier ∩ (curves l).carrier = ∅)
    (hD : IsOpen D) (hDr : interior (closure D) = D) (hfront : c₀.carrier = frontier D)
    (hEf : Disjoint (boundaryCrossingSet curves univ) (frontier D))
    {g : SmoothMetric M} (data : MetricGoodPhaseData g F)
    (hF : IsSmoothIsometricImmersion M g F) (n : PreferredNormal F)
    (hgeom : FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) F n)
    (hcurrent : ∀ p ∈ c₀.carrier, c₀.second F p ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize (c₀.second F p))
    (hfrontGeom : ∀ j p, p ∈ (curves j).carrier ∩ frontier D →
      0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n.vector p) ∧
      0 < c₀.crossing (curves j) F p)
    (hfirst : ∀ j p, p ∈ boundaryCrossingSet curves univ ∩ D → p ∈ (curves j).carrier →
      (fderiv ℝ (surfacePhaseTransition ((curves j).index : M) (curves j).phase
        (i : M) e) ((curves j).coordinate p) dy).1 ≠ 0)
    {P : Set SmallModes.Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ j, d.curve (curves j)) \ P,
      ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧ ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧
        (∀ x ∈ (⋃ j, d.curve (curves j)) ∩ N, f x = 0) ∧ fderiv ℝ f p dy ≠ 0)
    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + (fun p => (amp p)^2 • SmoothingAtlas.phaseDifferentialSquare phi p)) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ N : PreferredNormal W, FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) W N := by
  sorry

end SupportedPrimitivePatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

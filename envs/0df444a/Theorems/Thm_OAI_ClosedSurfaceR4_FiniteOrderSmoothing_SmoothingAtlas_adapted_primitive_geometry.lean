-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_adapted_primitive_geometry
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.adapted_primitive_geometry
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:51.792148+00:00
-- url     : https://prove2.me/theorems/ba8e360f-e8fb-4c56-a57e-a2f03d2b4e7c
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.adapted_primitive_geometry: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.adapted_primitive_geometry` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/AdaptedPrimitiveGeometry.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/AdaptedPrimitiveGeometry.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Filter Manifold`, `open scoped ContDiff Topology`, `open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame`):
--
--   ```lean
--   theorem adapted_primitive_geometry (j : B.centers)
--       {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
--       (n : PreferredNormal F)
--       (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
--       (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
--       {D : Set M} (hD : IsOpen D) (hqD : (j : M) ∈ D)
--       (hDs : closure D ⊆ (surfacePhaseChart (j : M) e).source)
--       {Ω : Set Base} (hΩ : IsOpen Ω)
--       (hDΩ : (surfacePhaseChart (j : M) e) '' closure D ⊆ Ω)
--       (hΩe : Ω ⊆ (surfacePhaseChart (j : M) e).target)
--       (hactive : ∀ x ∈ Ω, B.weight j ((surfacePhaseChart (j : M) e).symm x) ≠ 0)
--       {phi : Base → ℝ} (hphi : ContDiff ℝ ∞ phi)
--       (hphase : ∀ x, (JetPolynomial.realPhaseChart e x).1 = phi x)
--       (hconvex : ∀ x ∈ Ω, ∀ v : Base, v ≠ 0 →
--         0 < coordinateMetricHessian (coordinateMetric g (j : M)) phi
--           (coordinateChart (j : M) ((surfacePhaseChart (j : M) e).symm x)) v v)
--       (hboundary : ∀ x ∈ frontier ((surfacePhaseChart (j : M) e) '' D),
--         realSecondForm (B.phaseRealChartMap j e.symm F) dy dy x ≠ 0 ∧
--         normalize (realSecondForm (B.phaseRealChartMap j e.symm F) dy dy x) ≠ -n.inPhase (j : M) e x) :
--       ∃ (V : Set Base) (A : SmoothingAtlas M) (i : A.centers)
--         (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (U : Set Base),
--         IsOpen V ∧ IsCompact (closure V) ∧
--         (surfacePhaseChart (j : M) e) '' closure D ⊆ V ∧ closure V ⊆ Ω ∧
--         (i : M) = (j : M) ∧ (∀ x, f x = e x) ∧ (∀ x, f.symm x = e.symm x) ∧
--         ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ f.symm ∧
--         (∀ p ∈ closure D, 0 < A.weight i p) ∧
--         (∀ k p, p ∈ tsupport (A.weight k) → A.outer k =ᶠ[𝓝 p] (fun _ => 1)) ∧
--         (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ f.source ∧
--         MapsTo f f.source (baseEquiv ⁻¹' V) ∧
--         closure D ⊆ (surfacePhaseChart (i : M) f).source ∧
--         IsOpen U ∧ closure V ⊆ U ∧ U ⊆ Ω ∧
--         ContDiffOn ℝ ∞ (n.inPhase (j : M) e) U ∧
--         (∀ x ∈ U, Function.Injective (fderiv ℝ (A.phaseRealChartMap i f.symm F) x)) ∧
--         (∀ x ∈ U, coordDeriv dx (A.phaseRealChartMap i f.symm F) x ⬝ᵥ n.inPhase (j : M) e x = 0 ∧
--           coordDeriv dy (A.phaseRealChartMap i f.symm F) x ⬝ᵥ n.inPhase (j : M) e x = 0 ∧
--           n.inPhase (j : M) e x ⬝ᵥ n.inPhase (j : M) e x = 1) ∧
--         (∀ x ∈ U, 0 < coordinateMetricHessian
--           (inducedCoordinateMetric (A.phaseRealChartMap i f.symm F)) Prod.fst x dy dy) ∧
--         ∀ x ∈ closure V \ ((surfacePhaseChart (j : M) e) '' D),
--           realSecondForm (A.phaseRealChartMap i f.symm F) dy dy x ≠ 0 ∧
--           normalize (realSecondForm (A.phaseRealChartMap i f.symm F) dy dy x) ≠ -n.inPhase (j : M) e x
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.NormalFrame.Vec` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PreferredNormal` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.coordinateChart`, `OAI.ClosedSurfaceR4.coordinateMetric`, `OAI.ClosedSurfaceR4.PhaseGeometry.coordinateMetricHessian`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondForm`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv` and `OAI.ClosedSurfaceR4.VelocityFrame.normalize` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.realPhaseChart` and `OAI.ClosedSurfaceR4.RealModes.inducedCoordinateMetric` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.PreferredNormal.inPhase` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.surfacePhaseChart` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseRealChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.realize_sequence` and `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_supported_circular_patch` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/AdaptedPrimitiveGeometry.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.adapted_primitive_geometry)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

theorem adapted_primitive_geometry (j : B.centers)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hD : IsOpen D) (hqD : (j : M) ∈ D)
    (hDs : closure D ⊆ (surfacePhaseChart (j : M) e).source)
    {Ω : Set Base} (hΩ : IsOpen Ω)
    (hDΩ : (surfacePhaseChart (j : M) e) '' closure D ⊆ Ω)
    (hΩe : Ω ⊆ (surfacePhaseChart (j : M) e).target)
    (hactive : ∀ x ∈ Ω, B.weight j ((surfacePhaseChart (j : M) e).symm x) ≠ 0)
    {phi : Base → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hphase : ∀ x, (JetPolynomial.realPhaseChart e x).1 = phi x)
    (hconvex : ∀ x ∈ Ω, ∀ v : Base, v ≠ 0 →
      0 < coordinateMetricHessian (coordinateMetric g (j : M)) phi
        (coordinateChart (j : M) ((surfacePhaseChart (j : M) e).symm x)) v v)
    (hboundary : ∀ x ∈ frontier ((surfacePhaseChart (j : M) e) '' D),
      realSecondForm (B.phaseRealChartMap j e.symm F) dy dy x ≠ 0 ∧
      normalize (realSecondForm (B.phaseRealChartMap j e.symm F) dy dy x) ≠ -n.inPhase (j : M) e x) :
    ∃ (V : Set Base) (A : SmoothingAtlas M) (i : A.centers)
      (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (U : Set Base),
      IsOpen V ∧ IsCompact (closure V) ∧
      (surfacePhaseChart (j : M) e) '' closure D ⊆ V ∧ closure V ⊆ Ω ∧
      (i : M) = (j : M) ∧ (∀ x, f x = e x) ∧ (∀ x, f.symm x = e.symm x) ∧
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ f.symm ∧
      (∀ p ∈ closure D, 0 < A.weight i p) ∧
      (∀ k p, p ∈ tsupport (A.weight k) → A.outer k =ᶠ[𝓝 p] (fun _ => 1)) ∧
      (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ f.source ∧
      MapsTo f f.source (baseEquiv ⁻¹' V) ∧
      closure D ⊆ (surfacePhaseChart (i : M) f).source ∧
      IsOpen U ∧ closure V ⊆ U ∧ U ⊆ Ω ∧
      ContDiffOn ℝ ∞ (n.inPhase (j : M) e) U ∧
      (∀ x ∈ U, Function.Injective (fderiv ℝ (A.phaseRealChartMap i f.symm F) x)) ∧
      (∀ x ∈ U, coordDeriv dx (A.phaseRealChartMap i f.symm F) x ⬝ᵥ n.inPhase (j : M) e x = 0 ∧
        coordDeriv dy (A.phaseRealChartMap i f.symm F) x ⬝ᵥ n.inPhase (j : M) e x = 0 ∧
        n.inPhase (j : M) e x ⬝ᵥ n.inPhase (j : M) e x = 1) ∧
      (∀ x ∈ U, 0 < coordinateMetricHessian
        (inducedCoordinateMetric (A.phaseRealChartMap i f.symm F)) Prod.fst x dy dy) ∧
      ∀ x ∈ closure V \ ((surfacePhaseChart (j : M) e) '' D),
        realSecondForm (A.phaseRealChartMap i f.symm F) dy dy x ≠ 0 ∧
        normalize (realSecondForm (A.phaseRealChartMap i f.symm F) dy dy x) ≠ -n.inPhase (j : M) e x := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

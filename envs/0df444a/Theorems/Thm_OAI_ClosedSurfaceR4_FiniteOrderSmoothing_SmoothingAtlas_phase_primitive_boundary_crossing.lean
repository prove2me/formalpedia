-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phase_primitive_boundary_crossing
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_primitive_boundary_crossing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:33:06.023207+00:00
-- url     : https://prove2.me/theorems/6a939c26-75cc-4e7b-938a-560837d14ffe
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_primitive_boundary_crossing: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_primitive_boundary_crossing` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/PhasePrimitiveBoundaryGauss.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/PhasePrimitiveBoundaryGauss.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Topology Manifold`, `open JetPolynomial SurfaceJetCoordinates`):
--
--   ```lean
--   lemma phase_primitive_boundary_crossing (i : A.centers)
--       (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
--       {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
--       (h : SmoothMetric M) {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
--       {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
--       (htarget : h.inner = g.inner + A.bundleRestore A.tensorTriv i
--         (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
--       {x : SmallModes.Base} (hx : baseEquiv.symm x ∈ e.target)
--       (hactive : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
--       (hz : a x = 0) (hnonneg : ∀ᶠ y in 𝓝 x, 0 ≤ a y)
--       (hD : NormalFrame.gramDet
--         (SmallModes.coordDeriv SmallModes.dx (A.phaseRealChartMap i e.symm F) x)
--         (SmallModes.coordDeriv SmallModes.dy (A.phaseRealChartMap i e.symm F) x) ≠ 0)
--       (hB : RealModes.realSecondForm (A.phaseRealChartMap i e.symm F)
--         SmallModes.dy SmallModes.dy x ≠ 0) (b c : ℝ) :
--       let H := A.phaseRealChartMap i e.symm F
--       let κ := RealModes.coordinateGaussianCurvature
--         (RealModes.realMetric H SmallModes.dx SmallModes.dx)
--         (RealModes.realMetric H SmallModes.dx SmallModes.dy)
--         (RealModes.realMetric H SmallModes.dy SmallModes.dy) x
--       VelocityFrame.orderedCrossing H SmallModes.dy (b,c) x κ =
--         ((SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dx H) x ⬝ᵥ
--           VelocityFrame.normalize (RealModes.realSecondForm H SmallModes.dy SmallModes.dy x))*b +
--           Real.sqrt (RealModes.realSecondForm H SmallModes.dy SmallModes.dy x ⬝ᵥ
--             RealModes.realSecondForm H SmallModes.dy SmallModes.dy x)*c)^2 +
--           (RealModes.coordinateGauss (fun y => A.phaseMetricRead i e.symm h y 0)
--             (fun y => A.phaseMetricRead i e.symm h y 1)
--             (fun y => A.phaseMetricRead i e.symm h y 2) x)*b^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualSmul`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.bundleRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeight`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.fiberFromThree`, `OAI.ClosedSurfaceR4.RealModes.RField`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realMetric`, `OAI.ClosedSurfaceR4.RealModes.realSecondForm`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv` and `OAI.ClosedSurfaceR4.VelocityFrame.normalize` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.localizedTensorPullback` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryGaussReadDualAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryGaussReadFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryGaussReadFiberSpace` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseMetricRead` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.RealModes.coordinateGauss`, `OAI.ClosedSurfaceR4.RealModes.coordinateGaussianCurvature`, `OAI.ClosedSurfaceR4.VelocityFrame.orderedCrossing` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseRealChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_global_circular_primitive_normal` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/PhasePrimitiveBoundaryGauss.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_primitive_boundary_crossing)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
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
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryGaussReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryGaussReadFiberSpace
local instance boundaryGaussReadDualSmul_r086bbb_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryGaussReadFiberNormed
local instance boundaryGaussReadSectionNormed_r086bbb_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance boundaryGaussReadSectionSpace_r086bbb_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma phase_primitive_boundary_crossing (i : A.centers)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (h : SmoothMetric M) {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (htarget : h.inner = g.inner + A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {x : SmallModes.Base} (hx : baseEquiv.symm x ∈ e.target)
    (hactive : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
    (hz : a x = 0) (hnonneg : ∀ᶠ y in 𝓝 x, 0 ≤ a y)
    (hD : NormalFrame.gramDet
      (SmallModes.coordDeriv SmallModes.dx (A.phaseRealChartMap i e.symm F) x)
      (SmallModes.coordDeriv SmallModes.dy (A.phaseRealChartMap i e.symm F) x) ≠ 0)
    (hB : RealModes.realSecondForm (A.phaseRealChartMap i e.symm F)
      SmallModes.dy SmallModes.dy x ≠ 0) (b c : ℝ) :
    let H := A.phaseRealChartMap i e.symm F
    let κ := RealModes.coordinateGaussianCurvature
      (RealModes.realMetric H SmallModes.dx SmallModes.dx)
      (RealModes.realMetric H SmallModes.dx SmallModes.dy)
      (RealModes.realMetric H SmallModes.dy SmallModes.dy) x
    VelocityFrame.orderedCrossing H SmallModes.dy (b,c) x κ =
      ((SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dx H) x ⬝ᵥ
        VelocityFrame.normalize (RealModes.realSecondForm H SmallModes.dy SmallModes.dy x))*b +
        Real.sqrt (RealModes.realSecondForm H SmallModes.dy SmallModes.dy x ⬝ᵥ
          RealModes.realSecondForm H SmallModes.dy SmallModes.dy x)*c)^2 +
        (RealModes.coordinateGauss (fun y => A.phaseMetricRead i e.symm h y 0)
          (fun y => A.phaseMetricRead i e.symm h y 1)
          (fun y => A.phaseMetricRead i e.symm h y 2) x)*b^2 := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

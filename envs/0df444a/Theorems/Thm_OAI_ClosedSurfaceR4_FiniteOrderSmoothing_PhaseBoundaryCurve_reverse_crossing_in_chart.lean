-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_reverse_crossing_in_chart
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.reverse_crossing_in_chart
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:51:40.905936+00:00
-- url     : https://prove2.me/theorems/d1afe947-66bd-40fe-b76a-89722379ae5e
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.reverse_crossing_in_chart: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.reverse_crossing_in_chart` of [lean/OAI/Geometry/SurfaceImmersion/Atlas/PhaseCurvePairGeometry.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/PhaseCurvePairGeometry.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve`, with `open Set Filter Manifold`, `open scoped ContDiff Topology`, `open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame`):
--
--   ```lean
--   lemma reverse_crossing_in_chart {g : SmoothMetric M} {F : M → Space}
--       (hF : IsSmoothIsometricImmersion M g F) {p : M} (hc : p ∈ c.carrier) (hd : p ∈ d.carrier) :
--       let H := B.phaseRealChartMap d.index d.phase.symm F
--       c.crossing d F p = orderedCrossing H (c.directionIn d p) dy (d.coordinate p)
--         (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy)
--           (d.coordinate p))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` and `OAI.ClosedSurfaceR4.JetPolynomial.Base` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve`, `OAI.ClosedSurfaceR4.RealModes.RField`, `OAI.ClosedSurfaceR4.RealModes.realMetric`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.coordinate` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.RealModes.coordinateGaussianCurvature`, `OAI.ClosedSurfaceR4.VelocityFrame.orderedCrossing`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.crossing`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.directionIn` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseRealChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_circular_primitive_boundary_step` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/PhaseCurvePairGeometry.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.reverse_crossing_in_chart)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
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
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c d : PhaseBoundaryCurve B)

lemma reverse_crossing_in_chart {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) {p : M} (hc : p ∈ c.carrier) (hd : p ∈ d.carrier) :
    let H := B.phaseRealChartMap d.index d.phase.symm F
    c.crossing d F p = orderedCrossing H (c.directionIn d p) dy (d.coordinate p)
      (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy)
        (d.coordinate p)) := by
  sorry

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

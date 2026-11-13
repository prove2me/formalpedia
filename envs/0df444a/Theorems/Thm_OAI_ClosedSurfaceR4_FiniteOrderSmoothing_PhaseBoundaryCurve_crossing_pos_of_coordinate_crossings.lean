-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_crossing_pos_of_coordinate_crossings
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.crossing_pos_of_coordinate_crossings
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:50:56.258427+00:00
-- url     : https://prove2.me/theorems/cb098157-0bbc-481e-8713-f5e9e666cc69
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.crossing_pos_of_coordinate_crossings (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.crossing_pos_of_coordinate_crossings` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/PhasePreparedCrossings.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/PhasePreparedCrossings.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve`, with `open Set Filter Manifold`, `open scoped ContDiff Topology`, `open SurfaceJetCoordinates RealModes SmallModes VelocityFrame`):
--
--   ```lean
--   lemma crossing_pos_of_coordinate_crossings {g : SmoothMetric M} {F : M → Space}
--       (hF : IsSmoothIsometricImmersion M g F) {p : M}
--       (hc : p ∈ c.carrier) (hd : p ∈ d.carrier)
--       (hpos : ∀ v w : Base, v ≠ 0 → w ≠ 0 →
--         0 < orderedCrossing (coordinateMap F (c.index : M)) v w (coordinateChart (c.index : M) p)
--           (coordinateGaussianCurvature (realMetric (coordinateMap F (c.index : M)) dx dx)
--             (realMetric (coordinateMap F (c.index : M)) dx dy)
--             (realMetric (coordinateMap F (c.index : M)) dy dy) (coordinateChart (c.index : M) p))) :
--       0 < c.crossing d F p
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.coordinateChart`, `OAI.ClosedSurfaceR4.coordinateMap`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve`, `OAI.ClosedSurfaceR4.RealModes.realMetric`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.dx` and `OAI.ClosedSurfaceR4.SmallModes.dy` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.RealModes.coordinateGaussianCurvature`, `OAI.ClosedSurfaceR4.VelocityFrame.orderedCrossing` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.crossing` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_circular_starting_family` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/PhasePreparedCrossings.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.crossing_pos_of_coordinate_crossings)

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
open SurfaceJetCoordinates RealModes SmallModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c d : PhaseBoundaryCurve B)

lemma crossing_pos_of_coordinate_crossings {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) {p : M}
    (hc : p ∈ c.carrier) (hd : p ∈ d.carrier)
    (hpos : ∀ v w : Base, v ≠ 0 → w ≠ 0 →
      0 < orderedCrossing (coordinateMap F (c.index : M)) v w (coordinateChart (c.index : M) p)
        (coordinateGaussianCurvature (realMetric (coordinateMap F (c.index : M)) dx dx)
          (realMetric (coordinateMap F (c.index : M)) dx dy)
          (realMetric (coordinateMap F (c.index : M)) dy dy) (coordinateChart (c.index : M) p))) :
    0 < c.crossing d F p := by
  sorry

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

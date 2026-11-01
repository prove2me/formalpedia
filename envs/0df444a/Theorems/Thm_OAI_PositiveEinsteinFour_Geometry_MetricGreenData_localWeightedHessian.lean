-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_localWeightedHessian
-- name    : OAI.PositiveEinsteinFour.Geometry.MetricGreenData.localWeightedHessian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T18:41:56.230328+00:00
-- url     : https://prove2.me/theorems/54a60979-2d20-4c41-aaf8-b1d8347b709b
-- title:
--   OAI.PositiveEinsteinFour.Geometry.MetricGreenData.localWeightedHessian: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.localWeightedHessian` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Geometry`, with `open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory`, `open scoped BigOperators Manifold ContDiff`):
--
--   ```lean
--   theorem MetricGreenData.localWeightedHessian
--       {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
--       (d : MetricGreenData g μ) (o : OppositeWeylData d)
--       (hp : ShiftedCurvaturePositive g) (e : FrameBundle g)
--       (m : ℝ) (hm : 0 < m) (a : Vec) :
--       let A := plusWeyl g e.base e.frame
--       let U := minusWeyl g e.base e.frame
--       let X := plusWeylHessian g e.base e.frame
--       let L := weightTensor a (plusGradientTensor g e.base e.frame)
--       0 ≤ weightedQuadratic (generalOriginalCurvatureForm A U) m X L +
--         generalTraceCorrection A U (weylLaplacian A) m L +
--         generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Bianchi.Vec`, `OAI.PositiveEinsteinFour.Geometry.Mat3` and `OAI.PositiveEinsteinFour.TraceHessian.Hessian` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle` (definitions bundle `OAIQ091C007` of this split); `OAI.PositiveEinsteinFour.Geometry.minusWeyl` and `OAI.PositiveEinsteinFour.Geometry.plusWeyl` (definitions bundle `OAIQ091C008` of this split); `OAI.PositiveEinsteinFour.TraceHessian.weylLaplacian` (definitions bundle `OAIQ091C010` of this split); `OAI.PositiveEinsteinFour.Geometry.MetricGreenData`, `OAI.PositiveEinsteinFour.Geometry.OppositeWeylData` and `OAI.PositiveEinsteinFour.Geometry.plusWeylHessian` (definitions bundle `OAIQ091C014` of this split); `OAI.PositiveEinsteinFour.Geometry.ShiftedCurvaturePositive`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing`, `OAI.PositiveEinsteinFour.HighestHessian.generalOriginalCurvatureForm`, `OAI.PositiveEinsteinFour.HighestHessian.generalTraceCorrection`, `OAI.PositiveEinsteinFour.HighestHessian.highestProjection`, `OAI.PositiveEinsteinFour.HighestHessian.weightTensor` and `OAI.PositiveEinsteinFour.HighestHessian.weightedQuadratic` (definitions bundle `OAIQ091C015` of this split); `OAI.PositiveEinsteinFour.Geometry.plusGradientTensor` (definitions bundle `OAIQ091C018` of this split); `OAI.EinsteinFour.FourSpace`, `OAI.EinsteinFour.I4`, `OAI.EinsteinFour.SmoothMetric` and `OAI.PositiveEinsteinFour.Geometry.FrameBundle` (the published bundle `Def_EinsteinFour`).
--
--   **Used by.** The proof of `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.regularizedHessianGreen` of this split imports it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean (declaration OAI.PositiveEinsteinFour.Geometry.MetricGreenData.localWeightedHessian)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C018

section

attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem MetricGreenData.localWeightedHessian
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (hp : ShiftedCurvaturePositive g) (e : FrameBundle g)
    (m : ℝ) (hm : 0 < m) (a : Vec) :
    let A := plusWeyl g e.base e.frame
    let U := minusWeyl g e.base e.frame
    let X := plusWeylHessian g e.base e.frame
    let L := weightTensor a (plusGradientTensor g e.base e.frame)
    0 ≤ weightedQuadratic (generalOriginalCurvatureForm A U) m X L +
      generalTraceCorrection A U (weylLaplacian A) m L +
      generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m) := by
  sorry

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

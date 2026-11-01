-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_matrixGreen
-- name    : OAI.PositiveEinsteinFour.Geometry.MetricGreenData.matrixGreen
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T18:42:00.729139+00:00
-- url     : https://prove2.me/theorems/2e001400-6eb8-4e6b-a069-4da4188de254
-- title:
--   OAI.PositiveEinsteinFour.Geometry.MetricGreenData.matrixGreen: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.matrixGreen` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Geometry.MetricGreenData`, with `open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory`, `open scoped BigOperators Manifold ContDiff`):
--
--   ```lean
--   theorem matrixGreen (d : MetricGreenData g μ)
--       [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
--       (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
--       (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
--         (dm i ((d.flow i).map t e)) t) :
--       (∫ e, weightedQuadratic
--         (fun X => matrixHessianPairing (plusWeyl g e.base e.frame) X X)
--         (m e) (plusWeylHessian g e.base e.frame)
--         (weightTensor (WithLp.toLp 2 (fun i => dm i e))
--           (plusGradientTensor g e.base e.frame)) ∂μ) =
--       ∫ e, m e * (-10 * weylMatrixEnergy (plusWeyl g e.base e.frame)
--             (plusWeylGradient g e.base e.frame) -
--           3 * weylMatrixEnergy (traceFreeSquare (plusWeyl g e.base e.frame))
--             (plusWeylGradient g e.base e.frame) +
--           20 * weylCompressionEnergy (plusWeyl g e.base e.frame)
--             (plusWeylGradient g e.base e.frame)) +
--         (∑ i, dm i e * Matrix.trace (plusWeylGradient g e.base e.frame i *
--           (∑ j, plusWeylGradient g e.base e.frame j * plusWeylGradient g e.base e.frame j))) / 12 ∂μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Geometry.Mat3` and `OAI.PositiveEinsteinFour.TraceHessian.Hessian` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle` and `OAI.PositiveEinsteinFour.Geometry.FrameFlow` (definitions bundle `OAIQ091C007` of this split); `OAI.PositiveEinsteinFour.Geometry.plusWeyl` (definitions bundle `OAIQ091C008` of this split); `OAI.PositiveEinsteinFour.TraceHessian.traceFreeSquare` (definitions bundle `OAIQ091C010` of this split); `OAI.PositiveEinsteinFour.Geometry.MetricGreenData`, `OAI.PositiveEinsteinFour.Geometry.plusWeylGradient` and `OAI.PositiveEinsteinFour.Geometry.plusWeylHessian` (definitions bundle `OAIQ091C014` of this split); `OAI.PositiveEinsteinFour.Geometry.weylCompressionEnergy`, `OAI.PositiveEinsteinFour.Geometry.weylMatrixEnergy`, `OAI.PositiveEinsteinFour.HighestHessian.matrixHessianPairing`, `OAI.PositiveEinsteinFour.HighestHessian.weightTensor` and `OAI.PositiveEinsteinFour.HighestHessian.weightedQuadratic` (definitions bundle `OAIQ091C015` of this split); `OAI.PositiveEinsteinFour.Geometry.plusGradientTensor` (definitions bundle `OAIQ091C018` of this split); `OAI.EinsteinFour.FourSpace`, `OAI.EinsteinFour.I4`, `OAI.EinsteinFour.SmoothMetric`, `OAI.PositiveEinsteinFour.Geometry.FrameBundle` and `OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle` (the published bundle `Def_EinsteinFour`).
--
--   **Used by.** The proofs of `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.regularizedHessianGreen` and `OAI_PositiveEinsteinFour_Geometry_MetricGreenData_weightedHessianGreen` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean (declaration OAI.PositiveEinsteinFour.Geometry.MetricGreenData.matrixGreen)

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

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem matrixGreen (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    (∫ e, weightedQuadratic
      (fun X => matrixHessianPairing (plusWeyl g e.base e.frame) X X)
      (m e) (plusWeylHessian g e.base e.frame)
      (weightTensor (WithLp.toLp 2 (fun i => dm i e))
        (plusGradientTensor g e.base e.frame)) ∂μ) =
    ∫ e, m e * (-10 * weylMatrixEnergy (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame) -
        3 * weylMatrixEnergy (traceFreeSquare (plusWeyl g e.base e.frame))
          (plusWeylGradient g e.base e.frame) +
        20 * weylCompressionEnergy (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame)) +
      (∑ i, dm i e * Matrix.trace (plusWeylGradient g e.base e.frame i *
        (∑ j, plusWeylGradient g e.base e.frame j * plusWeylGradient g e.base e.frame j))) / 12 ∂μ := by
  sorry

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

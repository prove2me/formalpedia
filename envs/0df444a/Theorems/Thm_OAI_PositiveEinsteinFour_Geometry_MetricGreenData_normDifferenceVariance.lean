-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_normDifferenceVariance
-- name    : OAI.PositiveEinsteinFour.Geometry.MetricGreenData.normDifferenceVariance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T18:43:29.156121+00:00
-- url     : https://prove2.me/theorems/4e04122c-5ca8-457e-bdb0-d79a0b5c13f9
-- title:
--   OAI.PositiveEinsteinFour.Geometry.MetricGreenData.normDifferenceVariance: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.normDifferenceVariance` of [lean/OAI/Geometry/EinsteinFour/CurvatureTensors02.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/CurvatureTensors02.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Geometry`, with `open EinsteinFour TraceHessian MeasureTheory Filter`, `open scoped Manifold ContDiff _root_.Topology`):
--
--   ```lean
--   theorem MetricGreenData.normDifferenceVariance (d : MetricGreenData g μ)
--       (o : OppositeWeylData d) {orientation : FrameOrientation g}
--       (s : ScalarVarianceInputs d orientation) (hparallel : ParallelReflection d)
--       (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
--         normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
--       (∫ e, (normalizedBlockNorm (plusWeyl g e.base e.frame) -
--         normalizedBlockNorm (minusWeyl g e.base e.frame)) ^ 2 ∂μ) -
--       (∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) -
--         normalizedBlockNorm (minusWeyl g e.base e.frame) ∂μ) ^ 2 ≤
--       ∫ e, ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
--         blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2 /
--           scalarVarianceWeight g e ∂μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Bianchi.Vec` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle` (definitions bundle `OAIQ091C007` of this split); `OAI.PositiveEinsteinFour.Geometry.minusWeyl` and `OAI.PositiveEinsteinFour.Geometry.plusWeyl` (definitions bundle `OAIQ091C008` of this split); `OAI.PositiveEinsteinFour.Geometry.MetricGreenData`, `OAI.PositiveEinsteinFour.Geometry.OppositeWeylData`, `OAI.PositiveEinsteinFour.Geometry.ParallelReflection`, `OAI.PositiveEinsteinFour.Geometry.minusWeylGradient` and `OAI.PositiveEinsteinFour.Geometry.plusWeylGradient` (definitions bundle `OAIQ091C014` of this split); `OAI.PositiveEinsteinFour.Geometry.blockRadialGradient` and `OAI.PositiveEinsteinFour.Geometry.scalarVarianceWeight` (definitions bundle `OAIQ091C015` of this split); `OAI.PositiveEinsteinFour.Geometry.ScalarVarianceInputs` (definitions bundle `OAIQ091C018` of this split); `OAI.PositiveEinsteinFour.Geometry.normalizedBlockNorm` (definitions bundle `OAIQ091C036` of this split); `OAI.EinsteinFour.FourSpace`, `OAI.EinsteinFour.I4`, `OAI.EinsteinFour.SmoothMetric`, `OAI.PositiveEinsteinFour.Geometry.FrameBundle`, `OAI.PositiveEinsteinFour.Geometry.FrameOrientation` and `OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle` (the published bundle `Def_EinsteinFour`).
--
--   **Used by.** The proofs of `OAI_PositiveEinsteinFour_Geometry_models_of_actual_model_inputs`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/CurvatureTensors02.lean (declaration OAI.PositiveEinsteinFour.Geometry.MetricGreenData.normDifferenceVariance)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C018

section

attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ}

variable [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem MetricGreenData.normDifferenceVariance (d : MetricGreenData g μ)
    (o : OppositeWeylData d) {orientation : FrameOrientation g}
    (s : ScalarVarianceInputs d orientation) (hparallel : ParallelReflection d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, (normalizedBlockNorm (plusWeyl g e.base e.frame) -
      normalizedBlockNorm (minusWeyl g e.base e.frame)) ^ 2 ∂μ) -
    (∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) -
      normalizedBlockNorm (minusWeyl g e.base e.frame) ∂μ) ^ 2 ≤
    ∫ e, ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
      blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2 /
        scalarVarianceWeight g e ∂μ := by
  sorry

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

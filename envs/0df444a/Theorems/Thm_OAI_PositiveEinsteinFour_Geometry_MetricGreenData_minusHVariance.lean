-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_minusHVariance
-- name    : OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusHVariance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T18:42:41.614526+00:00
-- url     : https://prove2.me/theorems/8ee7093c-d254-41c5-9b67-35bf3b6bd84c
-- title:
--   OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusHVariance: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusHVariance` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Geometry`, with `open EinsteinFour TraceHessian MeasureTheory Filter`, `open scoped Manifold ContDiff _root_.Topology`):
--
--   ```lean
--   theorem MetricGreenData.minusHVariance
--       (d : MetricGreenData g μ) (o : OppositeWeylData d) {orientation : FrameOrientation g}
--       (s : ScalarVarianceInputs d orientation) (hparallel : ParallelReflection d)
--       (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
--         normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
--       (∫ e, MomentObstruction.H (normalizedBlockNorm (minusWeyl g e.base e.frame)) ^ 2 ∂μ) -
--         (∫ e, MomentObstruction.H (normalizedBlockNorm (minusWeyl g e.base e.frame)) ∂μ) ^ 2 ≤
--         (9 / 16 : ℝ) * ((∫ e, (normalizedBlockNorm (minusWeyl g e.base e.frame)) ^ 2 ∂μ) - ∫ e, normalizedBlockNorm (minusWeyl g e.base e.frame) ∂μ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.MomentObstruction.H` (definitions bundle `OAIQ091C004` of this split); `OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle` (definitions bundle `OAIQ091C007` of this split); `OAI.PositiveEinsteinFour.Geometry.minusWeyl` and `OAI.PositiveEinsteinFour.Geometry.plusWeyl` (definitions bundle `OAIQ091C008` of this split); `OAI.PositiveEinsteinFour.Geometry.MetricGreenData`, `OAI.PositiveEinsteinFour.Geometry.OppositeWeylData` and `OAI.PositiveEinsteinFour.Geometry.ParallelReflection` (definitions bundle `OAIQ091C014` of this split); `OAI.PositiveEinsteinFour.Geometry.ScalarVarianceInputs` (definitions bundle `OAIQ091C018` of this split); `OAI.PositiveEinsteinFour.Geometry.normalizedBlockNorm` (definitions bundle `OAIQ091C036` of this split); `OAI.EinsteinFour.FourSpace`, `OAI.EinsteinFour.I4`, `OAI.EinsteinFour.SmoothMetric`, `OAI.PositiveEinsteinFour.Geometry.FrameBundle`, `OAI.PositiveEinsteinFour.Geometry.FrameOrientation` and `OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle` (the published bundle `Def_EinsteinFour`).
--
--   **Used by.** The proofs of `OAI_PositiveEinsteinFour_Geometry_models_of_actual_model_inputs`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean (declaration OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusHVariance)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C018

section

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
  [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem MetricGreenData.minusHVariance
    (d : MetricGreenData g μ) (o : OppositeWeylData d) {orientation : FrameOrientation g}
    (s : ScalarVarianceInputs d orientation) (hparallel : ParallelReflection d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, MomentObstruction.H (normalizedBlockNorm (minusWeyl g e.base e.frame)) ^ 2 ∂μ) -
      (∫ e, MomentObstruction.H (normalizedBlockNorm (minusWeyl g e.base e.frame)) ∂μ) ^ 2 ≤
      (9 / 16 : ℝ) * ((∫ e, (normalizedBlockNorm (minusWeyl g e.base e.frame)) ^ 2 ∂μ) - ∫ e, normalizedBlockNorm (minusWeyl g e.base e.frame) ∂μ) := by
  sorry

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

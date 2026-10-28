-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_local_metric_radial_patch
-- name    : OAI.YauCounterexamples.exists_local_metric_radial_patch
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:02:42.811125+00:00
-- url     : https://prove2.me/theorems/f540ea44-26f6-4b7f-9357-860bac40e501
-- title:
--   OAI.YauCounterexamples.exists_local_metric_radial_patch: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_local_metric_radial_patch` of [lean/OAI/Geometry/SmoothYau/Geometry/RadialFiniteDualNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/RadialFiniteDualNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Function Filter Metric MeasureTheory Manifold Bundle`, `open scoped Topology ENNReal InnerProductSpace ContDiff`):
--
--   ```lean
--   theorem exists_local_metric_radial_patch (hdim : Module.finrank ℝ E = 3)
--       (g : SmoothMetric E E) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) {p : E}
--       (ha : coordinateMetricGradient g ψ p ≠ 0) :
--       ∃ (W : Set E) (y : E → ProfilePlane) (A : ℝ), IsOpen W ∧ p ∈ W ∧
--         ContDiff ℝ ∞ y ∧ 0 < A ∧ ∀ x ∈ W,
--         fderiv ℝ y x (coordinateMetricGradient g ψ x) = 0 ∧
--         (∀ v, twoCoframeForm (fderiv ℝ y x) v v ≤ 4*selfMetricFlat g x v v) ∧
--         (∀ v, fderiv ℝ ψ x v = 0 → selfMetricFlat g x v v ≤ 4*twoCoframeForm (fderiv ℝ y x) v v) ∧
--         A ≤ 2*actualProfileSpeed g ψ x ∧ actualProfileSpeed g ψ x/2 ≤ A
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CoordinateForm`, `OAI.YauCounterexamples.ProfilePlane` and `OAI.YauCounterexamples.selfMetricFlat` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.coordinateMetricGradient` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.twoCoframeForm` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.actualProfileSpeed` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.actual_metric_radial_finite` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/RadialFiniteDualNorm.lean (declaration OAI.YauCounterexamples.exists_local_metric_radial_patch)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A008
import Definitions.Def_OAIQ070A009

section

attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section

open Set Function Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ENNReal InnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem exists_local_metric_radial_patch (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) {p : E}
    (ha : coordinateMetricGradient g ψ p ≠ 0) :
    ∃ (W : Set E) (y : E → ProfilePlane) (A : ℝ), IsOpen W ∧ p ∈ W ∧
      ContDiff ℝ ∞ y ∧ 0 < A ∧ ∀ x ∈ W,
      fderiv ℝ y x (coordinateMetricGradient g ψ x) = 0 ∧
      (∀ v, twoCoframeForm (fderiv ℝ y x) v v ≤ 4*selfMetricFlat g x v v) ∧
      (∀ v, fderiv ℝ ψ x v = 0 → selfMetricFlat g x v v ≤ 4*twoCoframeForm (fderiv ℝ y x) v v) ∧
      A ≤ 2*actualProfileSpeed g ψ x ∧ actualProfileSpeed g ψ x/2 ≤ A := by
  sorry

end
end YauCounterexamples

end OAI
end

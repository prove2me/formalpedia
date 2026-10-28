-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_actual_preparation_neighborhood
-- name    : OAI.YauCounterexamples.exists_actual_preparation_neighborhood
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:01:35.148023+00:00
-- url     : https://prove2.me/theorems/17f46c7e-bc3b-4bb7-8049-cd4410611a20
-- title:
--   OAI.YauCounterexamples.exists_actual_preparation_neighborhood: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_actual_preparation_neighborhood` of [lean/OAI/Geometry/SmoothYau/Geometry/PrepDualNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/PrepDualNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter Metric`, `open scoped Topology InnerProductSpace`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory intervalIntegral`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology Manifold ContDiff ENNReal NNReal`, `open Set Filter Function Metric`, `open scoped Topology ContDiff`, `open Set Filter Function Metric`, `open scoped Topology ContDiff NNReal`, `open Set Filter Function Metric`, `open scoped Topology ContDiff NNReal`, `open Set Filter Function Metric`, `open scoped Topology ContDiff NNReal`, `open Set Filter Function Manifold Bundle`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   theorem exists_actual_preparation_neighborhood (hd : Module.finrank ℝ E = 3)
--       (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u) {p : E}
--       (ha : coordinateMetricGradient g u p ≠ 0) (hs : actualProfileStrict g u p) :
--       ∃ (W : Set E) (s : E → ℝ) (C : ℝ), IsOpen W ∧ p ∈ W ∧
--         ContDiff ℝ ∞ s ∧ 0 < C ∧ ∀ x ∈ W,
--           fderiv ℝ s x ≠ 0 ∧ fderiv ℝ s x (coordinateMetricGradient g u x) = 0 ∧
--           ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0) ∧
--           (∀ c ∈ Icc (-2*C) (2*C), quadraticPlaneStrict
--             (metricProfileTraceForm (selfMetricFlat g x)
--               (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
--               (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ∧
--           (∀ c ∈ Icc C (2*C), quadraticPlaneFull
--             (metricProfileTraceForm (selfMetricFlat g x)
--               (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
--               (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CoordinateForm`, `OAI.YauCounterexamples.ProfileForm`, `OAI.YauCounterexamples.actualCoordinateHessian` and `OAI.YauCounterexamples.selfMetricFlat` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.coordinateMetricGradient` and `OAI.YauCounterexamples.metricProfileTraceForm` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.profileRankOne`, `OAI.YauCounterexamples.quadraticPlaneFull` and `OAI.YauCounterexamples.quadraticPlaneStrict` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.actualProfileStrict` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_actual_metric_preparation` and `OAI.YauCounterexamples.actual_metric_profile_cycle` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/PrepDualNorm.lean (declaration OAI.YauCounterexamples.exists_actual_preparation_neighborhood)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009

section

attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
namespace YauCounterexamples
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_actual_preparation_neighborhood (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u) {p : E}
    (ha : coordinateMetricGradient g u p ≠ 0) (hs : actualProfileStrict g u p) :
    ∃ (W : Set E) (s : E → ℝ) (C : ℝ), IsOpen W ∧ p ∈ W ∧
      ContDiff ℝ ∞ s ∧ 0 < C ∧ ∀ x ∈ W,
        fderiv ℝ s x ≠ 0 ∧ fderiv ℝ s x (coordinateMetricGradient g u x) = 0 ∧
        ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0) ∧
        (∀ c ∈ Icc (-2*C) (2*C), quadraticPlaneStrict
          (metricProfileTraceForm (selfMetricFlat g x)
            (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
            (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ∧
        (∀ c ∈ Icc C (2*C), quadraticPlaneFull
          (metricProfileTraceForm (selfMetricFlat g x)
            (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
            (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) := by
  sorry

end YauCounterexamples

end

end OAI
end

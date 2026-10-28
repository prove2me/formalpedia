-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_sphericalBaseProfile_chart_margins
-- name    : OAI.YauCounterexamples.sphericalBaseProfile_chart_margins
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:47:01.359667+00:00
-- url     : https://prove2.me/theorems/3b33ddc9-36ba-4672-ad0c-8b0ba2ee73df
-- title:
--   OAI.YauCounterexamples.sphericalBaseProfile_chart_margins: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.sphericalBaseProfile_chart_margins` of [lean/OAI/Geometry/SmoothYau/Smoothness/SphericalBaseProfileRadius.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/SphericalBaseProfileRadius.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter Metric`, `open scoped Topology InnerProductSpace`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Manifold`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem sphericalBaseProfile_chart_margins (g : SmoothMetric (Euclidean 3) (Sphere 3))
--       (hg : IsRound g) (p : Sphere 3) (a b : Euclidean 4)
--       (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
--       (t : ℝ) (y : Euclidean 3)
--       (hr : (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) a)^2 +
--         (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) b)^2 ≤ 1/8) :
--       let G := sphereChartMetric g p
--       let f := sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm
--       (∀ v, -(1/4 : ℝ)*selfMetricFlat G y v v ≤ actualCoordinateHessian G f y v v) ∧
--       (∃ P : Submodule ℝ (Euclidean 3), Module.finrank ℝ P = 2 ∧
--         ∀ v ∈ P, (3/2 : ℝ)*selfMetricFlat G y v v ≤ actualCoordinateHessian G f y v v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CoordinateForm`, `OAI.YauCounterexamples.actualCoordinateHessian`, `OAI.YauCounterexamples.selfMetricFlat` and `OAI.YauCounterexamples.sphericalBaseProfile` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.roundChart` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.sphereChartMetric` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.sphereFrame` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.sphericalMetricGood_neighborhood` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/SphericalBaseProfileRadius.lean (declaration OAI.YauCounterexamples.sphericalBaseProfile_chart_margins)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
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
open Set Filter Manifold
open scoped Topology ContDiff
variable {n : ℕ}

theorem sphericalBaseProfile_chart_margins (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg : IsRound g) (p : Sphere 3) (a b : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (t : ℝ) (y : Euclidean 3)
    (hr : (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) a)^2 +
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) b)^2 ≤ 1/8) :
    let G := sphereChartMetric g p
    let f := sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm
    (∀ v, -(1/4 : ℝ)*selfMetricFlat G y v v ≤ actualCoordinateHessian G f y v v) ∧
    (∃ P : Submodule ℝ (Euclidean 3), Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, (3/2 : ℝ)*selfMetricFlat G y v v ≤ actualCoordinateHessian G f y v v) := by
  sorry

end

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
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter Manifold BoxIntegral
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

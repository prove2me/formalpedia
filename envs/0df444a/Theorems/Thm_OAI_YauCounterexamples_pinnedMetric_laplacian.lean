-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_pinnedMetric_laplacian
-- name    : OAI.YauCounterexamples.pinnedMetric_laplacian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:45:38.669116+00:00
-- url     : https://prove2.me/theorems/9ef8e044-156a-40f5-b70a-07e0bf2d409e
-- title:
--   OAI.YauCounterexamples.pinnedMetric_laplacian: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.pinnedMetric_laplacian` of [lean/OAI/Geometry/SmoothYau/Geometry/PinnedMetricJointGradientPair.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/PinnedMetricJointGradientPair.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function`, `open scoped Topology ContDiff Manifold SchwartzMap`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter NormedSpace`, `open scoped Topology`, `open scoped Matrix.Norms.Operator`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff Matrix`):
--
--   ```lean
--   theorem pinnedMetric_laplacian (g : SmoothMetric E M)
--       (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
--       (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
--         (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
--       (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
--       (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
--       {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
--       (hker : ∀ x, K x (metricGradient g u x) = 0) (t : ℝ) (x : M) :
--       laplaceBeltrami (pinnedMetric g K hK t) u x = laplaceBeltrami g u x
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.metricGradient` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.pinnedMetric` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple`, `OAI.YauCounterexamples.spherical_pin_near` and `OAI.YauCounterexamples.three_pin_near` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/PinnedMetricJointGradientPair.lean (declaration OAI.YauCounterexamples.pinnedMetric_laplacian)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff Matrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem pinnedMetric_laplacian (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hker : ∀ x, K x (metricGradient g u x) = 0) (t : ℝ) (x : M) :
    laplaceBeltrami (pinnedMetric g K hK t) u x = laplaceBeltrami g u x := by
  sorry

end

open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff Matrix BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

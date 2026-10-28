-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_three_cutoff_control_bounds
-- name    : OAI.YauCounterexamples.three_cutoff_control_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:27:38.292069+00:00
-- url     : https://prove2.me/theorems/f947a360-5d6a-4cde-980c-a443a30e120c
-- title:
--   OAI.YauCounterexamples.three_cutoff_control_bounds: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.three_cutoff_control_bounds` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric BoxIntegral`, `open scoped Topology ContDiff ENNReal InnerProductSpace`):
--
--   ```lean
--   lemma three_cutoff_control_bounds
--       (g : SmoothMetric ThreeModel ThreeManifold) (β χ v : ThreeManifold → ℝ)
--       (hχrange : ∀ q, χ q ∈ Icc (0:ℝ) 1) {η G Λ : ℝ}
--       (hηhalf : η < 1/2) (hvsmall : ∀ q, |v q-1| ≤ η)
--       (hGl : G*η < 1/32) (hGgrad : G*η < 1/4096)
--       (hΛ : 1 ≤ Λ)
--       (hctrl : ∀ q, |weightedLaplacian g β (cutoffFactor χ v) q| ≤ G*η ∧
--         Real.sqrt (coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) q) ≤ G*η) :
--       (∀ q, 1/2 ≤ cutoffFactor χ v q ∧ cutoffFactor χ v q ≤ 2) ∧
--       (∀ q, coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) q ≤ 1/4096) ∧
--       (∀ q, |Λ⁻¹*cutoffFactor χ v q*weightedLaplacian g β (cutoffFactor χ v) q| ≤ 1/16)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair`, `OAI.YauCounterexamples.cutoffFactor` and `OAI.YauCounterexamples.weightedLaplacian` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_exact_stage` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean (declaration OAI.YauCounterexamples.three_cutoff_control_bounds)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A003
import Definitions.Def_OAIQ070A004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

lemma three_cutoff_control_bounds
    (g : SmoothMetric ThreeModel ThreeManifold) (β χ v : ThreeManifold → ℝ)
    (hχrange : ∀ q, χ q ∈ Icc (0:ℝ) 1) {η G Λ : ℝ}
    (hηhalf : η < 1/2) (hvsmall : ∀ q, |v q-1| ≤ η)
    (hGl : G*η < 1/32) (hGgrad : G*η < 1/4096)
    (hΛ : 1 ≤ Λ)
    (hctrl : ∀ q, |weightedLaplacian g β (cutoffFactor χ v) q| ≤ G*η ∧
      Real.sqrt (coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) q) ≤ G*η) :
    (∀ q, 1/2 ≤ cutoffFactor χ v q ∧ cutoffFactor χ v q ≤ 2) ∧
    (∀ q, coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) q ≤ 1/4096) ∧
    (∀ q, |Λ⁻¹*cutoffFactor χ v q*weightedLaplacian g β (cutoffFactor χ v) q| ≤ 1/16) := by
  sorry

end YauCounterexamples
end

end OAI
end

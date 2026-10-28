-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_four_nodal_finite
-- name    : OAI.YauCounterexamples.four_nodal_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:42:41.652165+00:00
-- url     : https://prove2.me/theorems/f6474c74-0a57-43ec-b1de-e975bee7e42f
-- title:
--   OAI.YauCounterexamples.four_nodal_finite: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.four_nodal_finite` of [lean/OAI/Geometry/SmoothYau/ProductMetric/SphereProduct.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/ProductMetric/SphereProduct.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral MeasureTheory`, `open scoped Topology ContDiff Distributions ENNReal NNReal`):
--
--   ```lean
--   lemma four_nodal_finite (g : SmoothMetric FourModel FourManifold)
--       (u : ThreeManifold → ℝ) (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u)
--       (hr : ThreeRegular u) : nodalMeasure g 3 (u ∘ fourToThree) ≠ (∞ : ℝ≥0∞)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeRegular` and `OAI.YauCounterexamples.threeChartedSpace` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.fourToThree` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.FourManifold`, `OAI.YauCounterexamples.FourModel`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere`, `OAI.YauCounterexamples.fourChartedSpace`, `OAI.YauCounterexamples.fourIsManifold` and `OAI.YauCounterexamples.nodalMeasure` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_four_sign_nodal_real`, `OAI_YauCounterexamples_four_witnesses_unbounded` and `OAI.YauCounterexamples.sphere_two_torus_two` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/ProductMetric/SphereProduct.lean (declaration OAI.YauCounterexamples.four_nodal_finite)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral MeasureTheory
open scoped Topology ContDiff Distributions ENNReal NNReal
namespace YauCounterexamples
lemma four_nodal_finite (g : SmoothMetric FourModel FourManifold)
    (u : ThreeManifold → ℝ) (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u)
    (hr : ThreeRegular u) : nodalMeasure g 3 (u ∘ fourToThree) ≠ (∞ : ℝ≥0∞) := by
  sorry
end YauCounterexamples
end

end OAI
end

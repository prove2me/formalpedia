-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_laplaceBeltrami_four_lift
-- name    : OAI.YauCounterexamples.laplaceBeltrami_four_lift
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:08:41.840293+00:00
-- url     : https://prove2.me/theorems/7357f6b0-349b-468b-8a7b-9c63d31a996e
-- title:
--   OAI.YauCounterexamples.laplaceBeltrami_four_lift: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.laplaceBeltrami_four_lift` of [lean/OAI/Geometry/SmoothYau/ProductMetric/FourWaveThreeSmul.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/ProductMetric/FourWaveThreeSmul.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Manifold Bundle Function Matrix`, `open scoped Topology ContDiff Matrix.Norms.Elementwise`):
--
--   ```lean
--   lemma laplaceBeltrami_four_lift (g : SmoothMetric ThreeModel ThreeManifold) (u : ThreeManifold → ℝ)
--       (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (p : FourManifold) :
--       laplaceBeltrami (fourProductMetric g) (u ∘ fourToThree) p=laplaceBeltrami g u (fourToThree p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.fourToThree` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.fourProductMetric` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.FourManifold`, `OAI.YauCounterexamples.FourModel`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere`, `OAI.YauCounterexamples.fourChartedSpace`, `OAI.YauCounterexamples.fourIsManifold` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.sphere_two_torus_two` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/ProductMetric/FourWaveThreeSmul.lean (declaration OAI.YauCounterexamples.laplaceBeltrami_four_lift)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle Function Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma laplaceBeltrami_four_lift (g : SmoothMetric ThreeModel ThreeManifold) (u : ThreeManifold → ℝ)
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (p : FourManifold) :
    laplaceBeltrami (fourProductMetric g) (u ∘ fourToThree) p=laplaceBeltrami g u (fourToThree p) := by
  sorry
end

open Set Filter Manifold Bundle Function Matrix BoxIntegral MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise ENNReal NNReal

end YauCounterexamples
end

end OAI
end

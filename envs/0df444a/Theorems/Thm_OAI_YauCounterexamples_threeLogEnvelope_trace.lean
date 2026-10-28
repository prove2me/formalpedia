-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_threeLogEnvelope_trace
-- name    : OAI.YauCounterexamples.threeLogEnvelope_trace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:11:53.433425+00:00
-- url     : https://prove2.me/theorems/32080918-12a8-4a40-9860-781e1ae303d8
-- title:
--   OAI.YauCounterexamples.threeLogEnvelope_trace: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.threeLogEnvelope_trace` of [lean/OAI/Geometry/SmoothYau/Geometry/ThreeLogNormedSpace.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ThreeLogNormedSpace.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   lemma threeLogEnvelope_trace (p : ThreeManifold) (c : ℝ)
--       (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) :
--       actualProfileTraceForm (threeChartMetric threeBackgroundMetric p) (threeLogEnvelope p c) 0
--         (threeSphereDirection p 1) (threeSphereDirection p 1) =
--         c*(1-c^2)*(1-((p.1:Euclidean 3) 0)^2)/((p.1:Euclidean 3) 0)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CoordinateForm` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel` and `OAI.YauCounterexamples.ThreeProductModel` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.actualProfileTraceForm` and `OAI.YauCounterexamples.threeBackgroundMetric` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeSphereDirection` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.threeChartMetric` and `OAI.YauCounterexamples.threeLogEnvelope` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_profile_seed` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ThreeLogNormedSpace.lean (declaration OAI.YauCounterexamples.threeLogEnvelope_trace)

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
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
lemma threeLogEnvelope_trace (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) :
    actualProfileTraceForm (threeChartMetric threeBackgroundMetric p) (threeLogEnvelope p c) 0
      (threeSphereDirection p 1) (threeSphereDirection p 1) =
      c*(1-c^2)*(1-((p.1:Euclidean 3) 0)^2)/((p.1:Euclidean 3) 0)^2 := by
  sorry
end YauCounterexamples
end

end OAI
end

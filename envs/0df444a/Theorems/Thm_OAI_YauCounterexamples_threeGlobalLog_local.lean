-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_threeGlobalLog_local
-- name    : OAI.YauCounterexamples.threeGlobalLog_local
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:11:59.369931+00:00
-- url     : https://prove2.me/theorems/16df7f9b-23ee-46d4-bb75-7b8fb6ee0362
-- title:
--   OAI.YauCounterexamples.threeGlobalLog_local: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.threeGlobalLog_local` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeRobustProfileNormedSpace.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeRobustProfileNormedSpace.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   lemma threeGlobalLog_local :
--       threeGlobalLog ∘ (chartAt ThreeModel threeProfileCenter).symm =ᶠ[𝓝 0]
--         threeLogEnvelope threeProfileCenter threeEnvelopeExponent
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeProfileCenter` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.threeEnvelopeExponent` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.threeGlobalLog` and `OAI.YauCounterexamples.threeLogEnvelope` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_robust_seed` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeRobustProfileNormedSpace.lean (declaration OAI.YauCounterexamples.threeGlobalLog_local)

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
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeGlobalLog_local :
    threeGlobalLog ∘ (chartAt ThreeModel threeProfileCenter).symm =ᶠ[𝓝 0]
      threeLogEnvelope threeProfileCenter threeEnvelopeExponent := by
  sorry
end

open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

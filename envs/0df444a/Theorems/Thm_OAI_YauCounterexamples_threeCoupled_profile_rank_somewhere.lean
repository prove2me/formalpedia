-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_threeCoupled_profile_rank_somewhere
-- name    : OAI.YauCounterexamples.threeCoupled_profile_rank_somewhere
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:12:44.801211+00:00
-- url     : https://prove2.me/theorems/11b7ab82-98e3-4dae-9bf0-5fd49c7adf92
-- title:
--   OAI.YauCounterexamples.threeCoupled_profile_rank_somewhere: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.threeCoupled_profile_rank_somewhere` of [lean/OAI/Geometry/SmoothYau/Geometry/ChartPairRankTransfer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ChartPairRankTransfer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma threeCoupled_profile_rank_somewhere {m : ℕ} (hm : 1 ≤ m) :
--       ∃ x : ThreeModel, Function.Surjective (fderiv ℝ
--         (fun y => (threeCoupled threeCouplingRadius (4*m+1) ((chartAt ThreeModel threeProfileCenter).symm y),
--           coordinateGradientPair threeBackgroundMetric (threeCoupled threeCouplingRadius (4*m+1))
--             (threeCoupled threeCouplingRadius (4*m+1)) ((chartAt ThreeModel threeProfileCenter).symm y))) x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace`, `OAI.YauCounterexamples.threeIsManifold` and `OAI.YauCounterexamples.threeProfileCenter` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair` and `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.threeBackgroundMetric` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeCoupled` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.three_collar_rank` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ChartPairRankTransfer.lean (declaration OAI.YauCounterexamples.threeCoupled_profile_rank_somewhere)

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
open scoped Topology ContDiff
namespace YauCounterexamples
lemma threeCoupled_profile_rank_somewhere {m : ℕ} (hm : 1 ≤ m) :
    ∃ x : ThreeModel, Function.Surjective (fderiv ℝ
      (fun y => (threeCoupled threeCouplingRadius (4*m+1) ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair threeBackgroundMetric (threeCoupled threeCouplingRadius (4*m+1))
          (threeCoupled threeCouplingRadius (4*m+1)) ((chartAt ThreeModel threeProfileCenter).symm y))) x) := by
  sorry
end YauCounterexamples
end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_threeInteriorMeridianEnergy_deriv
-- name    : OAI.YauCounterexamples.exists_threeInteriorMeridianEnergy_deriv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:07:00.805048+00:00
-- url     : https://prove2.me/theorems/12d24955-d19c-48ba-ae35-39aebdee3b06
-- title:
--   OAI.YauCounterexamples.exists_threeInteriorMeridianEnergy_deriv: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_threeInteriorMeridianEnergy_deriv` of [lean/OAI/Geometry/SmoothYau/ProductMetric/ThreeInteriorMeridianNormedSpace.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/ProductMetric/ThreeInteriorMeridianNormedSpace.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Module Metric`, `open scoped Topology ContDiff InnerProductSpace Matrix`):
--
--   ```lean
--   lemma exists_threeInteriorMeridianEnergy_deriv (r : ℝ) (hr : 0 < r) (hr1 : r<1) {m : ℕ} (hm : 1 ≤ m) :
--       ∃ c ∈ Ioo 0 (Real.pi/2), deriv (threeInteriorMeridianEnergy r m) c ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.threeInteriorMeridianEnergy` (definitions bundle `OAIQ070A010` of this split).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.threeCoupled_profile_rank_somewhere` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/ProductMetric/ThreeInteriorMeridianNormedSpace.lean (declaration OAI.YauCounterexamples.exists_threeInteriorMeridianEnergy_deriv)

import Mathlib
import Definitions.Def_OAIQ070A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
lemma exists_threeInteriorMeridianEnergy_deriv (r : ℝ) (hr : 0 < r) (hr1 : r<1) {m : ℕ} (hm : 1 ≤ m) :
    ∃ c ∈ Ioo 0 (Real.pi/2), deriv (threeInteriorMeridianEnergy r m) c ≠ 0 := by
  sorry

end YauCounterexamples
end

end OAI
end

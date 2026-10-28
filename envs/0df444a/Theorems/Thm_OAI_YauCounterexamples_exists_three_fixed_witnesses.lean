-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_three_fixed_witnesses
-- name    : OAI.YauCounterexamples.exists_three_fixed_witnesses
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:42:42.885677+00:00
-- url     : https://prove2.me/theorems/66c6d64b-ef35-4371-a358-154add9d514d
-- title:
--   OAI.YauCounterexamples.exists_three_fixed_witnesses: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_three_fixed_witnesses` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral`, `open scoped Topology ContDiff Distributions ENNReal NNReal`):
--
--   ```lean
--   theorem exists_three_fixed_witnesses :
--       ∃ R : ℝ, 0<R ∧ ∃ g : SmoothMetric ThreeModel ThreeManifold,
--         ∀ n : ℕ, ThreeLargeWitness R g ((n:ℝ)+1) ((n:ℝ)+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.ThreeLargeWitness` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.sphere_two_torus_two` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean (declaration OAI.YauCounterexamples.exists_three_fixed_witnesses)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

theorem exists_three_fixed_witnesses :
    ∃ R : ℝ, 0<R ∧ ∃ g : SmoothMetric ThreeModel ThreeManifold,
      ∀ n : ℕ, ThreeLargeWitness R g ((n:ℝ)+1) ((n:ℝ)+1) := by
  sorry

end YauCounterexamples
end

end OAI
end

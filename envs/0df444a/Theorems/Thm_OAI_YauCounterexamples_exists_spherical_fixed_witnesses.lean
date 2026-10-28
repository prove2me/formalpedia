-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_spherical_fixed_witnesses
-- name    : OAI.YauCounterexamples.exists_spherical_fixed_witnesses
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:42:13.249688+00:00
-- url     : https://prove2.me/theorems/e4b5a079-5a34-47e1-b78e-52d39a1bdc3c
-- title:
--   OAI.YauCounterexamples.exists_spherical_fixed_witnesses: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_spherical_fixed_witnesses` of [lean/OAI/Geometry/SmoothYau/Limits/SphericalFixedFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/SphericalFixedFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral`, `open scoped Topology ContDiff Distributions ENNReal NNReal`):
--
--   ```lean
--   theorem exists_spherical_fixed_witnesses
--       (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
--       (N : Set (SmoothMetric (Euclidean 3) (Sphere 3))) (hN : IsSmoothNeighborhood g₀ N) :
--       ∃ g ∈ N, ∀ n : ℕ, SphericalLargeWitness g ((n:ℝ)+1) ((n:ℝ)+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.SphericalLargeWitness` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.IsSmoothNeighborhood`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.sphere_three` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/SphericalFixedFormNorm.lean (declaration OAI.YauCounterexamples.exists_spherical_fixed_witnesses)

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

theorem exists_spherical_fixed_witnesses
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (N : Set (SmoothMetric (Euclidean 3) (Sphere 3))) (hN : IsSmoothNeighborhood g₀ N) :
    ∃ g ∈ N, ∀ n : ℕ, SphericalLargeWitness g ((n:ℝ)+1) ((n:ℝ)+1) := by
  sorry

end YauCounterexamples
end

end OAI
end

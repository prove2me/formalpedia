-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_sphericalMetricGood_neighborhood
-- name    : OAI.YauCounterexamples.sphericalMetricGood_neighborhood
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:48:11.38872+00:00
-- url     : https://prove2.me/theorems/af037898-6604-4544-8698-88b34a625bed
-- title:
--   OAI.YauCounterexamples.sphericalMetricGood_neighborhood: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.sphericalMetricGood_neighborhood` of [lean/OAI/Geometry/SmoothYau/DifferentialEq/SphericalOpenFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/DifferentialEq/SphericalOpenFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral`, `open scoped Topology ContDiff Distributions`):
--
--   ```lean
--   lemma sphericalMetricGood_neighborhood (g₀ : SmoothMetric (Euclidean 3) (Sphere 3))
--       (hg₀ : IsRound g₀) : IsSmoothNeighborhood g₀ {g | SphericalMetricGood g}
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.SphericalMetricGood` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.IsSmoothNeighborhood`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_open_model` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/DifferentialEq/SphericalOpenFormNorm.lean (declaration OAI.YauCounterexamples.sphericalMetricGood_neighborhood)

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
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions
namespace YauCounterexamples
lemma sphericalMetricGood_neighborhood (g₀ : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg₀ : IsRound g₀) : IsSmoothNeighborhood g₀ {g | SphericalMetricGood g} := by
  sorry

end YauCounterexamples
end

end OAI
end

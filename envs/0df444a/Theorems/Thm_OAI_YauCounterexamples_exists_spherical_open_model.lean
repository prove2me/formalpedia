-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_spherical_open_model
-- name    : OAI.YauCounterexamples.exists_spherical_open_model
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:16:09.410789+00:00
-- url     : https://prove2.me/theorems/4ae7b3db-516a-4bdd-8052-ad8a91102783
-- title:
--   OAI.YauCounterexamples.exists_spherical_open_model: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_spherical_open_model` of [lean/OAI/Geometry/SmoothYau/DifferentialEq/SphericalOpenFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/DifferentialEq/SphericalOpenFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral`, `open scoped Topology ContDiff Distributions`):
--
--   ```lean
--   lemma exists_spherical_open_model (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
--       (N : Set (SmoothMetric (Euclidean 3) (Sphere 3))) (hN : IsSmoothNeighborhood g₀ N) :
--       ∃ O : Set SphericalTensor, IsOpen O ∧ 0 ∈ O ∧
--         ∀ H ∈ O, ∃ hp : H ∈ sphericalPositiveSet g₀,
--           sphericalTensorMetric g₀ ⟨H,hp⟩ ∈ N ∧ SphericalMetricGood (sphericalTensorMetric g₀ ⟨H,hp⟩)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.MetricForm` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.SphericalMetricGood`, `OAI.YauCounterexamples.SphericalPositiveTensor`, `OAI.YauCounterexamples.SphericalTensor`, `OAI.YauCounterexamples.sphericalAmbientFormNorm`, `OAI.YauCounterexamples.sphericalAmbientFormSpace`, `OAI.YauCounterexamples.sphericalPositiveSet` and `OAI.YauCounterexamples.sphericalTensorSupport` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.sphericalTensorMetric` (definitions bundle `OAIQ070A011` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.IsSmoothNeighborhood`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_fixed_witnesses` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/DifferentialEq/SphericalOpenFormNorm.lean (declaration OAI.YauCounterexamples.exists_spherical_open_model)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A011

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

local instance sphericalOpenFormNorm_r87a9c2_1 : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalOpenFormSpace_r87a9c2_1 : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
lemma exists_spherical_open_model (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (N : Set (SmoothMetric (Euclidean 3) (Sphere 3))) (hN : IsSmoothNeighborhood g₀ N) :
    ∃ O : Set SphericalTensor, IsOpen O ∧ 0 ∈ O ∧
      ∀ H ∈ O, ∃ hp : H ∈ sphericalPositiveSet g₀,
        sphericalTensorMetric g₀ ⟨H,hp⟩ ∈ N ∧ SphericalMetricGood (sphericalTensorMetric g₀ ⟨H,hp⟩) := by
  sorry
end YauCounterexamples
end

end OAI
end

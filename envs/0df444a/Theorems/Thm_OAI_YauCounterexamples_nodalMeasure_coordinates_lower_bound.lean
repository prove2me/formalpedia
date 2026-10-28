-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_nodalMeasure_coordinates_lower_bound
-- name    : OAI.YauCounterexamples.nodalMeasure_coordinates_lower_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:17:50.525477+00:00
-- url     : https://prove2.me/theorems/7e250531-cfaf-41ce-b6b8-1cde9473e99f
-- title:
--   OAI.YauCounterexamples.nodalMeasure_coordinates_lower_bound: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.nodalMeasure_coordinates_lower_bound` of [lean/OAI/Geometry/SmoothYau/NodalMeasure/SphericalNodalFinite.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/NodalMeasure/SphericalNodalFinite.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Metric Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff NNReal ENNReal`):
--
--   ```lean
--   theorem nodalMeasure_coordinates_lower_bound (g : SmoothMetric E M)
--       (p : M) {K : Set E} (hK : IsCompact K) (hKc : K ⊆ (chartAt E p).target) :
--       ∃ C : ℝ≥0, 0 < C ∧ ∀ u : M → ℝ, ∀ d : ℝ, 0 ≤ d →
--         Measure.hausdorffMeasure d (K ∩ {y | u ((chartAt E p).symm y) = 0}) ≤
--           (C : ℝ≥0∞)^d * nodalMeasure g d u
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.nodalMeasure` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_four_sign_nodal_real`, `OAI.YauCounterexamples.sphere_three`, `OAI.YauCounterexamples.sphere_two_torus_two` and `OAI_YauCounterexamples_spherical_sign_nodal_real` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/NodalMeasure/SphericalNodalFinite.lean (declaration OAI.YauCounterexamples.nodalMeasure_coordinates_lower_bound)

import Mathlib
import Definitions.Def_SmoothYau

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]

theorem nodalMeasure_coordinates_lower_bound (g : SmoothMetric E M)
    (p : M) {K : Set E} (hK : IsCompact K) (hKc : K ⊆ (chartAt E p).target) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ u : M → ℝ, ∀ d : ℝ, 0 ≤ d →
      Measure.hausdorffMeasure d (K ∩ {y | u ((chartAt E p).symm y) = 0}) ≤
        (C : ℝ≥0∞)^d * nodalMeasure g d u := by
  sorry

end

open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral MeasureTheory
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

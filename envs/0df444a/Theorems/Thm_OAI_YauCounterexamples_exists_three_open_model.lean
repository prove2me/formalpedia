-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_three_open_model
-- name    : OAI.YauCounterexamples.exists_three_open_model
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:16:26.024362+00:00
-- url     : https://prove2.me/theorems/6b1c265b-0633-478c-a0ca-9b253b250910
-- title:
--   OAI.YauCounterexamples.exists_three_open_model: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_three_open_model` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric`, `open scoped Topology ContDiff Distributions`):
--
--   ```lean
--   lemma exists_three_open_model (R : ℝ) (N : Set (SmoothMetric ThreeModel ThreeManifold))
--       (hN : IsSmoothNeighborhood threeBackgroundMetric N) :
--       ∃ O : Set (ThreeTensor R), IsOpen O ∧ 0∈O ∧
--         ∀ H∈O, ∃ hp : H∈threePositiveSet R, threeTensorMetric R ⟨H,hp⟩∈N
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.MetricForm` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.ThreePositiveTensor`, `OAI.YauCounterexamples.ThreeTensor`, `OAI.YauCounterexamples.threeAmbientFormNorm`, `OAI.YauCounterexamples.threeAmbientFormSpace`, `OAI.YauCounterexamples.threeBackgroundMetric`, `OAI.YauCounterexamples.threePositiveSet` and `OAI.YauCounterexamples.threeTensorSupport` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeTensorMetric` (definitions bundle `OAIQ070A011` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsSmoothNeighborhood`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_fixed_witnesses` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean (declaration OAI.YauCounterexamples.exists_three_open_model)

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
namespace YauCounterexamples

section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions
attribute [local instance] OAI.YauCounterexamples.threeAmbientFormNorm
attribute [local instance] OAI.YauCounterexamples.threeAmbientFormSpace
lemma exists_three_open_model (R : ℝ) (N : Set (SmoothMetric ThreeModel ThreeManifold))
    (hN : IsSmoothNeighborhood threeBackgroundMetric N) :
    ∃ O : Set (ThreeTensor R), IsOpen O ∧ 0∈O ∧
      ∀ H∈O, ∃ hp : H∈threePositiveSet R, threeTensorMetric R ⟨H,hp⟩∈N := by
  sorry
end

open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

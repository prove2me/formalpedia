-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_compact_normal_image_neighborhood
-- name    : OAI.YauCounterexamples.compact_normal_image_neighborhood
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:35:02.579456+00:00
-- url     : https://prove2.me/theorems/fb175e15-46f1-4699-8732-92dfe0fc8c76
-- title:
--   OAI.YauCounterexamples.compact_normal_image_neighborhood: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.compact_normal_image_neighborhood` of [lean/OAI/Geometry/SmoothYau/Limits/CompactNormalImageNeighborhood.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CompactNormalImageNeighborhood.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma compact_normal_image_neighborhood
--       (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       {K V : Set NormalWaveSpace} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
--       ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ < r →
--         normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) (normalWaveEquiv x) ∈ V
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.metricChristoffel` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.normalJetMap` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.metricFrameSet` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CompactNormalImageNeighborhood.lean (declaration OAI.YauCounterexamples.compact_normal_image_neighborhood)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

lemma compact_normal_image_neighborhood
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K V : Set NormalWaveSpace} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ < r →
      normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) (normalWaveEquiv x) ∈ V := by
  sorry
end YauCounterexamples
end

end OAI
end

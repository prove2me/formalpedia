-- Prove2me | Theorems.Thm_OAI_Paper170_cycle_pairing_of_coordinates
-- name    : OAI.Paper170.cycle_pairing_of_coordinates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T04:42:22.76177+00:00
-- url     : https://prove2.me/theorems/b7be738b-d33d-4523-aaea-238d02b2e961
-- title:
--   OAI.Paper170.cycle_pairing_of_coordinates: intermediate lemma from OpenAI, The crossing number of complete graphs
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Paper170.complete_graph_crossing_number`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The crossing number of complete graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Paper170.cycle_pairing_of_coordinates` of [lean/OAI/Combinatorics/CompleteCrossing/CompleteCrossing/CycleIdentity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/CompleteCrossing/CycleIdentity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Paper170`, with `open Paper170Geometry`):
--
--   ```lean
--   theorem cycle_pairing_of_coordinates (N : NormalizedDrawing graph) (O : SpokeOrders N)
--       (V : VertexTruncation N.toContinuousDrawing) (C : TruncatedSpokeCoordinates V)
--       (hnode : ∀v (e f : IncidentEdges graph v),
--         Zarankiewicz.orderSign (C.node v e) (C.node v f) = spokeComparison O v e.val f.val)
--       (z z' : Edge → ℝ) (hz : ∀v, boundary graph z v = 0) (hz' : ∀v, boundary graph z' v = 0) :
--       edgePairing (cycleIntersection O) z z' = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Paper170.NormalizedDrawing`, `OAI.Paper170.SpokeOrders`, `OAI.Paper170.boundary`, `OAI.Paper170.cycleIntersection`, `OAI.Paper170.edgePairing`, `OAI.Paper170.spokeComparison` and `OAI.Paper170Geometry.IncidentEdges` (definitions bundle `OAIQ4Cc000` of this split); `OAI.Zarankiewicz.orderSign` (definitions bundle `OAIQ4Cc001` of this split); `OAI.Paper170Geometry.TruncatedSpokeCoordinates` and `OAI.Paper170Geometry.VertexTruncation` (definitions bundle `OAIQ4Cc002` of this split); `OAI.Paper170.Graph` and `OAI.Paper170.AdmissibleDrawing` (the published bundle `Def_CompleteCrossing`).
--
--   **Used by.** The proof of `OAI.Paper170.complete_graph_lower_bound` of this split imports it.
-- source:
--   OpenAI, The crossing number of complete graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-graphs-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/CompleteCrossing/CycleIdentity.lean (declaration OAI.Paper170.cycle_pairing_of_coordinates)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_CompleteCrossing
import Definitions.Def_OAIQ4Cc002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace Paper170
open Paper170Geometry
variable {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
  {graph : Graph Vertex Edge}

theorem cycle_pairing_of_coordinates (N : NormalizedDrawing graph) (O : SpokeOrders N)
    (V : VertexTruncation N.toContinuousDrawing) (C : TruncatedSpokeCoordinates V)
    (hnode : ∀v (e f : IncidentEdges graph v),
      Zarankiewicz.orderSign (C.node v e) (C.node v f) = spokeComparison O v e.val f.val)
    (z z' : Edge → ℝ) (hz : ∀v, boundary graph z v = 0) (hz' : ∀v, boundary graph z' v = 0) :
    edgePairing (cycleIntersection O) z z' = 0 := by
  sorry

end Paper170

end
end

end OAI
end

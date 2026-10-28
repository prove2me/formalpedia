-- Prove2me | Theorems.Thm_OAI_Zarankiewicz_TruncatedSpokeCoordinates_exists_cross_type_radius
-- name    : OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cross_type_radius
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T13:15:30.596614+00:00
-- url     : https://prove2.me/theorems/116d23d4-9ee7-4c51-96d7-fe356a93ecb8
-- title:
--   OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cross_type_radius: intermediate lemma from OpenAI, The crossing number of complete bipartite graphs
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Zarankiewicz.mainTarget_proof`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The crossing number of complete bipartite graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cross_type_radius` of [lean/OAI/Combinatorics/Crossing/UniformCrossTypeGeometry.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/UniformCrossTypeGeometry.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Zarankiewicz.TruncatedSpokeCoordinates`):
--
--   ```lean
--   theorem exists_cross_type_radius (hnorm : NoAdjacentCrossings D) :
--       ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ →
--         (∀ j (f : IncidentEdges j) e (i : Fin (V.pieces e)),
--           ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
--             (C.shiftedPort j f ε) (C.tangentPort j f ε)) ∧
--         (∀ j (c d : IncidentEdges j) e (i : Fin (V.pieces e)),
--           ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
--             (C.shiftedPort j c ε) (C.shiftedPort j d ε)) ∧
--         (∀ j (a b : IncidentEdges j) e (i : Fin (V.pieces e)),
--           ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b)
--             (shiftedTrack (V.vertices e) (V.pieces e) ε i.val)
--             (shiftedTrack (V.vertices e) (V.pieces e) ε (i.val+1))) ∧
--         (∀ j k (a b : IncidentEdges j) (f : IncidentEdges k),
--           ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b)
--             (C.shiftedPort k f ε) (C.tangentPort k f ε)) ∧
--         (∀ j k (a b : IncidentEdges j) (c d : IncidentEdges k), a ≠ b → c ≠ d →
--           SegmentPairTransverse (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε)) ∧
--         (∀ j k, j ≠ k → ∀ (a b : IncidentEdges j) (c d : IncidentEdges k),
--           ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Zarankiewicz.ClosedSegmentsMeet`, `OAI.Zarankiewicz.IncidentEdges` and `OAI.Zarankiewicz.SegmentPairTransverse` (definitions bundle `OAIB3Zr000` of this split); `OAI.Zarankiewicz.NoAdjacentCrossings` (definitions bundle `OAIB3Zr001` of this split); `OAI.Zarankiewicz.TruncatedSpokeCoordinates`, `OAI.Zarankiewicz.VertexTruncation`, `OAI.Zarankiewicz.shiftedTrack`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.shiftedPort`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.tangentPort`, `OAI.Zarankiewicz.VertexTruncation.pieces`, `OAI.Zarankiewicz.VertexTruncation.spokePort` and `OAI.Zarankiewicz.VertexTruncation.vertices` (definitions bundle `OAIB3Zr002` of this split); `OAI.Zarankiewicz.AdmissibleDrawing`, `OAI.Zarankiewicz.BipartiteEdge` and `OAI.Zarankiewicz.BipartiteVertex` (the published bundle `Def_BipartiteCrossing`).
--
--   **Used by.** The proofs of `OAI.Zarankiewicz.TruncatedSpokeCoordinates.additive_detector_relation`, `OAI_Zarankiewicz_TruncatedSpokeCoordinates_closed_cycle_matrix_sum`, `OAI_Zarankiewicz_TruncatedSpokeCoordinates_exists_chord_edge_radius` and `OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cycle_block_radius` of this split import it.
-- source:
--   OpenAI, The crossing number of complete bipartite graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/UniformCrossTypeGeometry.lean (declaration OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cross_type_radius)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_cross_type_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ →
      (∀ j (f : IncidentEdges j) e (i : Fin (V.pieces e)),
        ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
          (C.shiftedPort j f ε) (C.tangentPort j f ε)) ∧
      (∀ j (c d : IncidentEdges j) e (i : Fin (V.pieces e)),
        ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
          (C.shiftedPort j c ε) (C.shiftedPort j d ε)) ∧
      (∀ j (a b : IncidentEdges j) e (i : Fin (V.pieces e)),
        ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b)
          (shiftedTrack (V.vertices e) (V.pieces e) ε i.val)
          (shiftedTrack (V.vertices e) (V.pieces e) ε (i.val+1))) ∧
      (∀ j k (a b : IncidentEdges j) (f : IncidentEdges k),
        ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b)
          (C.shiftedPort k f ε) (C.tangentPort k f ε)) ∧
      (∀ j k (a b : IncidentEdges j) (c d : IncidentEdges k), a ≠ b → c ≠ d →
        SegmentPairTransverse (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε)) ∧
      (∀ j k, j ≠ k → ∀ (a b : IncidentEdges j) (c d : IncidentEdges k),
        ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε)) := by
  sorry

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

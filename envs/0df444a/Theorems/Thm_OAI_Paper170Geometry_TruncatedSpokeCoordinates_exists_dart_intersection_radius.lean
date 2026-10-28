-- Prove2me | Theorems.Thm_OAI_Paper170Geometry_TruncatedSpokeCoordinates_exists_dart_intersection_radius
-- name    : OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_dart_intersection_radius
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T04:42:23.901907+00:00
-- url     : https://prove2.me/theorems/5c737a37-a542-4182-b924-0c2fb28c8634
-- title:
--   OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_dart_intersection_radius: intermediate lemma from OpenAI, The crossing number of complete graphs
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Paper170.complete_graph_crossing_number`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The crossing number of complete graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_dart_intersection_radius` of [lean/OAI/Combinatorics/CompleteCrossing/CompleteCrossing/CycleIntersections.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/CompleteCrossing/CycleIntersections.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Paper170Geometry.TruncatedSpokeCoordinates`, with `open Zarankiewicz`, `open scoped Classical`):
--
--   ```lean
--   theorem exists_dart_intersection_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D)
--       (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
--       ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
--         (∀ a b : OrientedDart graph,
--           (V.dartTrackChain a).Transverse (C.shiftedDartChain b ε) ∧
--           polygonIntersection (V.dartTrackChain a).vertices (C.shiftedDartChain b ε).vertices
--             (V.dartTrackChain a).pieces (C.shiftedDartChain b ε).pieces=
--               dartSign a*dartSign b*V.signedIntersection (OrientedDart.edge a) (OrientedDart.edge b)) ∧
--         (∀ j (a b : IncidentEdges graph j) d,
--           (V.chordChain j a b).Transverse (C.shiftedDartChain d ε) ∧
--           polygonIntersection (V.chordChain j a b).vertices (C.shiftedDartChain d ε).vertices
--             (V.chordChain j a b).pieces (C.shiftedDartChain d ε).pieces=0) ∧
--         (∀ j (a b : IncidentEdges graph j) d,
--           (V.dartTrackChain d).Transverse (C.shiftedChordChain j a b ε) ∧
--           polygonIntersection (V.dartTrackChain d).vertices (C.shiftedChordChain j a b ε).vertices
--             (V.dartTrackChain d).pieces (C.shiftedChordChain j a b ε).pieces=0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Paper170Geometry.IncidentEdges`, `OAI.Paper170Geometry.LocallyStraightCrossings`, `OAI.Paper170Geometry.LocallyTransverseCrossings`, `OAI.Paper170Geometry.NoAdjacentCrossings`, `OAI.Paper170Geometry.OrientedDart`, `OAI.Zarankiewicz.Plane`, `OAI.Paper170Geometry.OrientedDart.fst`, `OAI.Paper170Geometry.OrientedDart.snd` and `OAI.Zarankiewicz.PolygonalChain` (definitions bundle `OAIQ4Cc000` of this split); `OAI.Paper170Geometry.TruncatedSpokeCoordinates`, `OAI.Paper170Geometry.VertexTruncation`, `OAI.Paper170Geometry.dartSign`, `OAI.Paper170Geometry.dartSourceIncident`, `OAI.Paper170Geometry.dartTargetIncident`, `OAI.Zarankiewicz.polygonIntersection`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.shiftedChordChain`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.shiftedDartChain`, `OAI.Paper170Geometry.TruncatedSpokeCoordinates.shiftedPort`, `OAI.Paper170Geometry.VertexTruncation.chordChain`, `OAI.Paper170Geometry.VertexTruncation.dartTrackChain`, `OAI.Paper170Geometry.VertexTruncation.signedIntersection`, `OAI.Paper170Geometry.VertexTruncation.spokePort` and `OAI.Zarankiewicz.PolygonalChain.Transverse` (definitions bundle `OAIQ4Cc002` of this split); `OAI.Paper170.AdmissibleDrawing` and `OAI.Paper170.Graph` (the published bundle `Def_CompleteCrossing`).
--
--   **Used by.** The proof of `OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_cycle_block_radius` of this split imports it.
-- source:
--   OpenAI, The crossing number of complete graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-graphs-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/CompleteCrossing/CycleIntersections.lean (declaration OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_dart_intersection_radius)

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
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_dart_intersection_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
      (∀ a b : OrientedDart graph,
        (V.dartTrackChain a).Transverse (C.shiftedDartChain b ε) ∧
        polygonIntersection (V.dartTrackChain a).vertices (C.shiftedDartChain b ε).vertices
          (V.dartTrackChain a).pieces (C.shiftedDartChain b ε).pieces=
            dartSign a*dartSign b*V.signedIntersection (OrientedDart.edge a) (OrientedDart.edge b)) ∧
      (∀ j (a b : IncidentEdges graph j) d,
        (V.chordChain j a b).Transverse (C.shiftedDartChain d ε) ∧
        polygonIntersection (V.chordChain j a b).vertices (C.shiftedDartChain d ε).vertices
          (V.chordChain j a b).pieces (C.shiftedDartChain d ε).pieces=0) ∧
      (∀ j (a b : IncidentEdges graph j) d,
        (V.dartTrackChain d).Transverse (C.shiftedChordChain j a b ε) ∧
        polygonIntersection (V.dartTrackChain d).vertices (C.shiftedChordChain j a b ε).vertices
          (V.dartTrackChain d).pieces (C.shiftedChordChain j a b ε).pieces=0) := by
  sorry

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

end OAI
end

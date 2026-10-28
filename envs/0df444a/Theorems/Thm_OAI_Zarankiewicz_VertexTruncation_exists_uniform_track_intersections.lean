-- Prove2me | Theorems.Thm_OAI_Zarankiewicz_VertexTruncation_exists_uniform_track_intersections
-- name    : OAI.Zarankiewicz.VertexTruncation.exists_uniform_track_intersections
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T13:17:14.030513+00:00
-- url     : https://prove2.me/theorems/3ae92717-7ec5-43b2-971d-66f1485b639b
-- title:
--   OAI.Zarankiewicz.VertexTruncation.exists_uniform_track_intersections: intermediate lemma from OpenAI, The crossing number of complete bipartite graphs
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Zarankiewicz.mainTarget_proof`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The crossing number of complete bipartite graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Zarankiewicz.VertexTruncation.exists_uniform_track_intersections` of [lean/OAI/Combinatorics/Crossing/UniformTrackPerturbation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/UniformTrackPerturbation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Zarankiewicz.VertexTruncation`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem exists_uniform_track_intersections (V : VertexTruncation D.toContinuousDrawing)
--       (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
--       ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ e f : BipartiteEdge m n,
--         polygonIntersection (V.vertices e) (shiftedTrack (V.vertices f) (V.pieces f) t) (V.pieces e) (V.pieces f) =
--           if e=f then 0 else polygonIntersection (V.vertices e) (V.vertices f) (V.pieces e) (V.pieces f)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Zarankiewicz.NoAdjacentCrossings` (definitions bundle `OAIB3Zr001` of this split); `OAI.Zarankiewicz.LocallyStraightCrossings`, `OAI.Zarankiewicz.LocallyTransverseCrossings`, `OAI.Zarankiewicz.VertexTruncation`, `OAI.Zarankiewicz.polygonIntersection`, `OAI.Zarankiewicz.shiftedTrack`, `OAI.Zarankiewicz.VertexTruncation.pieces` and `OAI.Zarankiewicz.VertexTruncation.vertices` (definitions bundle `OAIB3Zr002` of this split); `OAI.Zarankiewicz.AdmissibleDrawing` and `OAI.Zarankiewicz.BipartiteEdge` (the published bundle `Def_BipartiteCrossing`).
--
--   **Used by.** The proof of `OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cycle_block_radius` of this split imports it.
-- source:
--   OpenAI, The crossing number of complete bipartite graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/UniformTrackPerturbation.lean (declaration OAI.Zarankiewicz.VertexTruncation.exists_uniform_track_intersections)

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
namespace Zarankiewicz.VertexTruncation
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem exists_uniform_track_intersections (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ e f : BipartiteEdge m n,
      polygonIntersection (V.vertices e) (shiftedTrack (V.vertices f) (V.pieces f) t) (V.pieces e) (V.pieces f) =
        if e=f then 0 else polygonIntersection (V.vertices e) (V.vertices f) (V.pieces e) (V.pieces f) := by
  sorry

end Zarankiewicz.VertexTruncation

end

end OAI
end

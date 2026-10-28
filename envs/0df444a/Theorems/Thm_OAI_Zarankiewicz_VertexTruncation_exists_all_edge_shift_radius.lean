-- Prove2me | Theorems.Thm_OAI_Zarankiewicz_VertexTruncation_exists_all_edge_shift_radius
-- name    : OAI.Zarankiewicz.VertexTruncation.exists_all_edge_shift_radius
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T13:16:49.065267+00:00
-- url     : https://prove2.me/theorems/22df1b60-f2da-4a43-8bd5-f1874421275d
-- title:
--   OAI.Zarankiewicz.VertexTruncation.exists_all_edge_shift_radius: intermediate lemma from OpenAI, The crossing number of complete bipartite graphs
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Zarankiewicz.mainTarget_proof`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The crossing number of complete bipartite graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Zarankiewicz.VertexTruncation.exists_all_edge_shift_radius` of [lean/OAI/Combinatorics/Crossing/UniformTrackPerturbation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/UniformTrackPerturbation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Zarankiewicz.VertexTruncation`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem exists_all_edge_shift_radius (V : VertexTruncation D.toContinuousDrawing)
--       (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
--       ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ e f : BipartiteEdge m n,
--         ∀ i : Fin (V.pieces e), ∀ j : Fin (V.pieces f),
--           SegmentPairTransverse (V.vertices e i.val) (V.vertices e (i.val+1))
--             (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
--             (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) ∧
--           segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
--             (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
--             (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) =
--             if e=f then 0 else segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
--               (V.vertices f j.val) (V.vertices f (j.val+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Zarankiewicz.SegmentPairTransverse` (definitions bundle `OAIB3Zr000` of this split); `OAI.Zarankiewicz.NoAdjacentCrossings` (definitions bundle `OAIB3Zr001` of this split); `OAI.Zarankiewicz.LocallyStraightCrossings`, `OAI.Zarankiewicz.LocallyTransverseCrossings`, `OAI.Zarankiewicz.VertexTruncation`, `OAI.Zarankiewicz.segmentCrossingSign`, `OAI.Zarankiewicz.shiftedTrack`, `OAI.Zarankiewicz.VertexTruncation.pieces` and `OAI.Zarankiewicz.VertexTruncation.vertices` (definitions bundle `OAIB3Zr002` of this split); `OAI.Zarankiewicz.AdmissibleDrawing` and `OAI.Zarankiewicz.BipartiteEdge` (the published bundle `Def_BipartiteCrossing`).
--
--   **Used by.** The proofs of `OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cycle_block_radius` and `OAI.Zarankiewicz.VertexTruncation.exists_uniform_track_intersections` of this split import it.
-- source:
--   OpenAI, The crossing number of complete bipartite graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/UniformTrackPerturbation.lean (declaration OAI.Zarankiewicz.VertexTruncation.exists_all_edge_shift_radius)

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

theorem exists_all_edge_shift_radius (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ e f : BipartiteEdge m n,
      ∀ i : Fin (V.pieces e), ∀ j : Fin (V.pieces f),
        SegmentPairTransverse (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) ∧
        segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) =
          if e=f then 0 else segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
            (V.vertices f j.val) (V.vertices f (j.val+1)) := by
  sorry

end Zarankiewicz.VertexTruncation

end

end OAI
end

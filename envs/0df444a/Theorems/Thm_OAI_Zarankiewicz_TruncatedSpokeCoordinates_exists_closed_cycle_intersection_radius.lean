-- Prove2me | Theorems.Thm_OAI_Zarankiewicz_TruncatedSpokeCoordinates_exists_closed_cycle_intersection_radius
-- name    : OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_closed_cycle_intersection_radius
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T13:15:28.391728+00:00
-- url     : https://prove2.me/theorems/37f5b3dd-37ef-4a44-8c10-9ae09bf140e5
-- title:
--   OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_closed_cycle_intersection_radius: intermediate lemma from OpenAI, The crossing number of complete bipartite graphs
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Zarankiewicz.mainTarget_proof`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The crossing number of complete bipartite graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_closed_cycle_intersection_radius` of [lean/OAI/Combinatorics/Crossing/GlobalCycleIntersection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/GlobalCycleIntersection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Zarankiewicz.TruncatedSpokeCoordinates`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem exists_closed_cycle_intersection_radius (hnorm : NoAdjacentCrossings D)
--       (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
--       ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
--         ∀ (d f : ℕ → (completeBipartite m n).Dart)
--           (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
--           (N K : ℕ), d N=d 0 → f K=f 0 →
--           (∀ i, i < N → bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i)) →
--           (∀ j, j < K → bipartiteDartEdge (f (j+1)) ≠ bipartiteDartEdge (f j)) →
--         ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
--           (bipartiteDartSign (d i)*bipartiteDartSign (f j)*
--             V.signedIntersection (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j))+
--               C.passageIntersection d f hd hf i j ε)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Zarankiewicz.NoAdjacentCrossings`, `OAI.Zarankiewicz.bipartiteDartEdge`, `OAI.Zarankiewicz.bipartiteDartSign` and `OAI.Zarankiewicz.completeBipartite` (definitions bundle `OAIB3Zr001` of this split); `OAI.Zarankiewicz.LocallyStraightCrossings`, `OAI.Zarankiewicz.LocallyTransverseCrossings`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates`, `OAI.Zarankiewicz.VertexTruncation`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.passageIntersection` and `OAI.Zarankiewicz.VertexTruncation.signedIntersection` (definitions bundle `OAIB3Zr002` of this split); `OAI.Zarankiewicz.AdmissibleDrawing` and `OAI.Zarankiewicz.BipartiteEdge` (the published bundle `Def_BipartiteCrossing`).
--
--   **Used by.** The proof of `OAI.Zarankiewicz.TruncatedSpokeCoordinates.additive_detector_relation` of this split imports it.
-- source:
--   OpenAI, The crossing number of complete bipartite graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/GlobalCycleIntersection.lean (declaration OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_closed_cycle_intersection_radius)

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
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_closed_cycle_intersection_radius (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
      ∀ (d f : ℕ → (completeBipartite m n).Dart)
        (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
        (N K : ℕ), d N=d 0 → f K=f 0 →
        (∀ i, i < N → bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i)) →
        (∀ j, j < K → bipartiteDartEdge (f (j+1)) ≠ bipartiteDartEdge (f j)) →
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        (bipartiteDartSign (d i)*bipartiteDartSign (f j)*
          V.signedIntersection (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j))+
            C.passageIntersection d f hd hf i j ε)=0 := by
  sorry

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

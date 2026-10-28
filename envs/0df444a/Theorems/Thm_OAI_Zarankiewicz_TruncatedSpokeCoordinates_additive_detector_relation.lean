-- Prove2me | Theorems.Thm_OAI_Zarankiewicz_TruncatedSpokeCoordinates_additive_detector_relation
-- name    : OAI.Zarankiewicz.TruncatedSpokeCoordinates.additive_detector_relation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T13:18:23.099896+00:00
-- url     : https://prove2.me/theorems/7ee6f8e6-5fc5-4a70-b88f-095730cbaa15
-- title:
--   OAI.Zarankiewicz.TruncatedSpokeCoordinates.additive_detector_relation: intermediate lemma from OpenAI, The crossing number of complete bipartite graphs
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Zarankiewicz.mainTarget_proof`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The crossing number of complete bipartite graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Zarankiewicz.TruncatedSpokeCoordinates.additive_detector_relation` of [lean/OAI/Combinatorics/Crossing/VertexOrderDetector.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/VertexOrderDetector.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Zarankiewicz.TruncatedSpokeCoordinates`):
--
--   ```lean
--   theorem additive_detector_relation (hnorm : NoAdjacentCrossings D)
--       (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
--       (s : ℕ) (node : Fin n → ℝ) (hn : Function.Injective node) (hcard : n=2*s+1)
--       (i k i₀ : Fin m) :
--       rankDetector s node (edgeBlock C.cycleIntersectionMatrix i k)-
--         rankDetector s node (edgeBlock C.cycleIntersectionMatrix i i₀)-
--         rankDetector s node (edgeBlock C.cycleIntersectionMatrix i₀ k)+
--         rankDetector s node (edgeBlock C.cycleIntersectionMatrix i₀ i₀)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Zarankiewicz.BiExponent` (definitions bundle `OAIB3Zr000` of this split); `OAI.Zarankiewicz.NoAdjacentCrossings` and `OAI.Zarankiewicz.edgeBlock` (definitions bundle `OAIB3Zr001` of this split); `OAI.Zarankiewicz.LocallyStraightCrossings`, `OAI.Zarankiewicz.LocallyTransverseCrossings`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates`, `OAI.Zarankiewicz.VertexTruncation` and `OAI.Zarankiewicz.TruncatedSpokeCoordinates.cycleIntersectionMatrix` (definitions bundle `OAIB3Zr002` of this split); `OAI.Zarankiewicz.rankDetector` (definitions bundle `OAIB3Zr004` of this split); `OAI.Zarankiewicz.AdmissibleDrawing` (the published bundle `Def_BipartiteCrossing`).
--
--   **Used by.** The proof of `OAI.Zarankiewicz.TruncatedSpokeCoordinates.odd_normalized_crossing_lower_bound` of this split imports it.
-- source:
--   OpenAI, The crossing number of complete bipartite graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/VertexOrderDetector.lean (declaration OAI.Zarankiewicz.TruncatedSpokeCoordinates.additive_detector_relation)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr004

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

theorem additive_detector_relation (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (s : ℕ) (node : Fin n → ℝ) (hn : Function.Injective node) (hcard : n=2*s+1)
    (i k i₀ : Fin m) :
    rankDetector s node (edgeBlock C.cycleIntersectionMatrix i k)-
      rankDetector s node (edgeBlock C.cycleIntersectionMatrix i i₀)-
      rankDetector s node (edgeBlock C.cycleIntersectionMatrix i₀ k)+
      rankDetector s node (edgeBlock C.cycleIntersectionMatrix i₀ i₀)=0 := by
  sorry

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
end

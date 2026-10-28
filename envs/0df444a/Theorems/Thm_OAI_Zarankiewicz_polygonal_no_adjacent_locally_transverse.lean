-- Prove2me | Theorems.Thm_OAI_Zarankiewicz_polygonal_no_adjacent_locally_transverse
-- name    : OAI.Zarankiewicz.polygonal_no_adjacent_locally_transverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T13:17:14.719573+00:00
-- url     : https://prove2.me/theorems/43df700d-a165-4479-bfca-990c8390c100
-- title:
--   OAI.Zarankiewicz.polygonal_no_adjacent_locally_transverse: intermediate lemma from OpenAI, The crossing number of complete bipartite graphs
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Zarankiewicz.mainTarget_proof`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The crossing number of complete bipartite graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Zarankiewicz.polygonal_no_adjacent_locally_transverse` of [lean/OAI/Combinatorics/Crossing/LocallyTransverseNormalization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/LocallyTransverseNormalization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Zarankiewicz`):
--
--   ```lean
--   theorem polygonal_no_adjacent_locally_transverse (D : AdmissibleDrawing m n) :
--       ∃ A : AdmissibleDrawing m n, crossingCount A ≤ crossingCount D ∧
--         (∀ e, HasFiniteAffineCover (A.edge e)) ∧ NoAdjacentCrossings A ∧
--         LocallyStraightCrossings A ∧ LocallyTransverseCrossings A
--   ```
--
--   **Definitions.** The statement is written with `OAI.Zarankiewicz.NoAdjacentCrossings` (definitions bundle `OAIB3Zr001` of this split); `OAI.Zarankiewicz.HasFiniteAffineCover`, `OAI.Zarankiewicz.LocallyStraightCrossings` and `OAI.Zarankiewicz.LocallyTransverseCrossings` (definitions bundle `OAIB3Zr002` of this split); `OAI.Zarankiewicz.AdmissibleDrawing`, `OAI.Zarankiewicz.BipartiteEdge`, `OAI.Zarankiewicz.crossingCount` and `OAI.Zarankiewicz.ContinuousDrawing` (the published bundle `Def_BipartiteCrossing`).
--
--   **Used by.** The proof of `OAI.Zarankiewicz.mainTarget_proof` of this split imports it.
-- source:
--   OpenAI, The crossing number of complete bipartite graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/LocallyTransverseNormalization.lean (declaration OAI.Zarankiewicz.polygonal_no_adjacent_locally_transverse)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr002

section

attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem polygonal_no_adjacent_locally_transverse (D : AdmissibleDrawing m n) :
    ∃ A : AdmissibleDrawing m n, crossingCount A ≤ crossingCount D ∧
      (∀ e, HasFiniteAffineCover (A.edge e)) ∧ NoAdjacentCrossings A ∧
      LocallyStraightCrossings A ∧ LocallyTransverseCrossings A := by
  sorry

end Zarankiewicz

end

end OAI
end

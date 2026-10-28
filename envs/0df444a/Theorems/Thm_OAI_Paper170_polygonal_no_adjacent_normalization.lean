-- Prove2me | Theorems.Thm_OAI_Paper170_polygonal_no_adjacent_normalization
-- name    : OAI.Paper170.polygonal_no_adjacent_normalization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T04:40:08.410778+00:00
-- url     : https://prove2.me/theorems/a7665ee8-0632-43cc-9fe0-16cbb918bfbe
-- title:
--   OAI.Paper170.polygonal_no_adjacent_normalization: intermediate lemma from OpenAI, The crossing number of complete graphs
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Paper170.complete_graph_crossing_number`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The crossing number of complete graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Paper170.polygonal_no_adjacent_normalization` of [lean/OAI/Combinatorics/CompleteCrossing/CompleteCrossing/Normalization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/CompleteCrossing/Normalization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Paper170`):
--
--   ```lean
--   theorem polygonal_no_adjacent_normalization (D : AdmissibleDrawing G) :
--       ∃ N : NormalizedDrawing G, crossingCount N.toAdmissibleDrawing ≤ crossingCount D
--   ```
--
--   **Definitions.** The statement is written with `OAI.Paper170.NormalizedDrawing` (definitions bundle `OAIQ4Cc000` of this split); `OAI.Paper170.AdmissibleDrawing`, `OAI.Paper170.Graph` and `OAI.Paper170.crossingCount` (the published bundle `Def_CompleteCrossing`).
--
--   **Used by.** The proof of `OAI.Paper170.complete_graph_lower_bound` of this split imports it.
-- source:
--   OpenAI, The crossing number of complete graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-graphs-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/CompleteCrossing/Normalization.lean (declaration OAI.Paper170.polygonal_no_adjacent_normalization)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_CompleteCrossing
import Definitions.Def_OAIQ4Cc000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace Paper170
variable {V E : Type} [Fintype V] [Fintype E] (G : Graph V E)

theorem polygonal_no_adjacent_normalization (D : AdmissibleDrawing G) :
    ∃ N : NormalizedDrawing G, crossingCount N.toAdmissibleDrawing ≤ crossingCount D := by
  sorry

end Paper170

end
end

end OAI
end

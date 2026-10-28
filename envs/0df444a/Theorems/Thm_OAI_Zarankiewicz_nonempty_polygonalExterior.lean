-- Prove2me | Theorems.Thm_OAI_Zarankiewicz_nonempty_polygonalExterior
-- name    : OAI.Zarankiewicz.nonempty_polygonalExterior
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T13:16:46.894915+00:00
-- url     : https://prove2.me/theorems/4149efe8-4a17-4f63-91d9-3ff365abe97c
-- title:
--   OAI.Zarankiewicz.nonempty_polygonalExterior: intermediate lemma from OpenAI, The crossing number of complete bipartite graphs
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Zarankiewicz.mainTarget_proof`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The crossing number of complete bipartite graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Zarankiewicz.nonempty_polygonalExterior` of [lean/OAI/Combinatorics/Crossing/PolygonalExterior.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/PolygonalExterior.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Zarankiewicz`):
--
--   ```lean
--   theorem nonempty_polygonalExterior (C : DrawingPassages D) : Nonempty (PolygonalExterior C)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Zarankiewicz.DrawingPassages` and `OAI.Zarankiewicz.FiniteIntersectionDrawing` (definitions bundle `OAIB3Zr000` of this split); `OAI.Zarankiewicz.PolygonalExterior` (definitions bundle `OAIB3Zr002` of this split).
--
--   **Used by.** The proofs of `OAI.Zarankiewicz.finite_intersection_normalization` and `OAI.Zarankiewicz.polygonal_no_adjacent_locally_transverse` of this split import it.
-- source:
--   OpenAI, The crossing number of complete bipartite graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/PolygonalExterior.lean (declaration OAI.Zarankiewicz.nonempty_polygonalExterior)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIB3Zr002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem nonempty_polygonalExterior (C : DrawingPassages D) : Nonempty (PolygonalExterior C) := by
  sorry

end Zarankiewicz

end

end OAI
end

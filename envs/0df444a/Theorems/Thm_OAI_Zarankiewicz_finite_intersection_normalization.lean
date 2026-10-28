-- Prove2me | Theorems.Thm_OAI_Zarankiewicz_finite_intersection_normalization
-- name    : OAI.Zarankiewicz.finite_intersection_normalization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T13:16:12.51896+00:00
-- url     : https://prove2.me/theorems/f6970e80-2c57-4769-a20c-b52d7ad4cbcd
-- title:
--   OAI.Zarankiewicz.finite_intersection_normalization: intermediate lemma from OpenAI, The crossing number of complete bipartite graphs
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Zarankiewicz.mainTarget_proof`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The crossing number of complete bipartite graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Zarankiewicz.finite_intersection_normalization` of [lean/OAI/Combinatorics/Crossing/PolygonalNormalization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/PolygonalNormalization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Zarankiewicz`):
--
--   ```lean
--   theorem finite_intersection_normalization {m n : ℕ} (D : FiniteIntersectionDrawing m n) :
--       ∃ D' : AdmissibleDrawing m n,
--         (∀ e, HasFiniteAffineCover (D'.edge e)) ∧ crossingCount D' ≤ finiteCrossingCount D
--   ```
--
--   **Definitions.** The statement is written with `OAI.Zarankiewicz.FiniteIntersectionDrawing` (definitions bundle `OAIB3Zr000` of this split); `OAI.Zarankiewicz.HasFiniteAffineCover` (definitions bundle `OAIB3Zr002` of this split); `OAI.Zarankiewicz.finiteCrossingCount` (definitions bundle `OAIB3Zr003` of this split); `OAI.Zarankiewicz.AdmissibleDrawing`, `OAI.Zarankiewicz.BipartiteEdge`, `OAI.Zarankiewicz.crossingCount` and `OAI.Zarankiewicz.ContinuousDrawing` (the published bundle `Def_BipartiteCrossing`).
--
--   **Used by.** The proof of `OAI.Zarankiewicz.polygonal_no_adjacent_locally_transverse` of this split imports it.
-- source:
--   OpenAI, The crossing number of complete bipartite graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/PolygonalNormalization.lean (declaration OAI.Zarankiewicz.finite_intersection_normalization)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr002
import Definitions.Def_OAIB3Zr003

section

attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem finite_intersection_normalization {m n : ℕ} (D : FiniteIntersectionDrawing m n) :
    ∃ D' : AdmissibleDrawing m n,
      (∀ e, HasFiniteAffineCover (D'.edge e)) ∧ crossingCount D' ≤ finiteCrossingCount D := by
  sorry

end Zarankiewicz

end

end OAI
end

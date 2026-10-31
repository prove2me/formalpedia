-- Prove2me | Theorems.Thm_OAI_CycleClique_finite_range_verified
-- name    : OAI.CycleClique.finite_range_verified
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T17:26:14.331507+00:00
-- url     : https://prove2.me/theorems/52cf50e3-9020-4b43-827d-932d21511126
-- title:
--   OAI.CycleClique.finite_range_verified: intermediate lemma from OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CycleClique.finite_range_verified` of [lean/OAI/Combinatorics/Ramsey/CycleClique/FiniteRange.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Ramsey/CycleClique/FiniteRange.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CycleClique`, with `open scoped SimpleGraph`, `open scoped SimpleGraph`):
--
--   ```lean
--   theorem finite_range_verified {k t : ℕ} (hk : 5 ≤ k) (ht : 3 ≤ t)
--       (htk : t ≤ k) (ht8 : t ≤ 8) (hhalf : k/2 ≤ t) :
--       ∀ D ∈ patternChoices t (k-t) [], PatternVerified k t D
--   ```
--
--   **Definitions.** The statement is written with `OAI.CycleClique.PatternVerified` (definitions bundle `OAIQ107D000` of this split); `OAI.CycleClique.patternChoices` (definitions bundle `OAIQ107D007` of this split).
--
--   **Used by.** The proof of `OAI.CycleClique.thm_main` of this split imports it.
-- source:
--   OpenAI, Cycle-clique Ramsey numbers, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 189; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Ramsey/CycleClique/FiniteRange.lean (declaration OAI.CycleClique.finite_range_verified)

import Mathlib
import Definitions.Def_OAIQ107D000
import Definitions.Def_OAIQ107D007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

open scoped SimpleGraph

theorem finite_range_verified {k t : ℕ} (hk : 5 ≤ k) (ht : 3 ≤ t)
    (htk : t ≤ k) (ht8 : t ≤ 8) (hhalf : k/2 ≤ t) :
    ∀ D ∈ patternChoices t (k-t) [], PatternVerified k t D := by
  sorry

end CycleClique

end OAI
end

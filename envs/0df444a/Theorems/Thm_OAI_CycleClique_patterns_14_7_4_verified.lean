-- Prove2me | Theorems.Thm_OAI_CycleClique_patterns_14_7_4_verified
-- name    : OAI.CycleClique.patterns_14_7_4_verified
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T19:31:11.630995+00:00
-- url     : https://prove2.me/theorems/f90b23f6-65f2-432d-8e62-51637cfa826e
-- title:
--   OAI.CycleClique.patterns_14_7_4_verified: intermediate lemma from OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CycleClique.patterns_14_7_4_verified` of [lean/OAI/Combinatorics/Ramsey/CycleClique/Patterns14x7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Ramsey/CycleClique/Patterns14x7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CycleClique`, with `open scoped SimpleGraph`):
--
--   ```lean
--   theorem patterns_14_7_4_verified : ∀ D ∈ patterns_14_7_4, PatternVerified 14 7 D
--   ```
--
--   **Definitions.** The statement is written with `OAI.CycleClique.PatternVerified` (definitions bundle `OAIQ107D000` of this split); `OAI.CycleClique.patterns_14_7_4` (definitions bundle `OAIQ107D007` of this split).
--
--   **Used by.** The proof of `OAI.CycleClique.finite_patterns_14_7` of this split imports it.
-- source:
--   OpenAI, Cycle-clique Ramsey numbers, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 189; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Ramsey/CycleClique/Patterns14x7.lean (declaration OAI.CycleClique.patterns_14_7_4_verified)

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

theorem patterns_14_7_4_verified : ∀ D ∈ patterns_14_7_4, PatternVerified 14 7 D := by
  sorry

end CycleClique

end OAI
end

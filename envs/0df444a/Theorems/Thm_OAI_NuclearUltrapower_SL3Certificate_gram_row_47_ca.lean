-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_47_ca
-- name    : OAI.NuclearUltrapower.SL3Certificate.gram_row_47_ca
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:52:15.796758+00:00
-- url     : https://prove2.me/theorems/8a55a9dc-9b58-488f-87b7-cc1340173a1f
-- title:
--   OAI.NuclearUltrapower.SL3Certificate.gram_row_47_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SL3Certificate`):
--
--   ```lean
--   theorem gram_row_47_ca : columns.map (dot q47) = g47
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SL3Certificate.columns`, `OAI.NuclearUltrapower.SL3Certificate.dot` and `OAI.NuclearUltrapower.SL3Certificate.q47` (definitions bundle `OAIQ229C004` of this split); `OAI.NuclearUltrapower.SL3Certificate.g47` (definitions bundle `OAIQ229C005` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.gramData_roots_ca` of this split imports it.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ229C004
import Definitions.Def_OAIQ229C005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SL3Certificate
theorem gram_row_47_ca : columns.map (dot q47) = g47 := by
  sorry
end NuclearUltrapower.SL3Certificate
end

end OAI
end

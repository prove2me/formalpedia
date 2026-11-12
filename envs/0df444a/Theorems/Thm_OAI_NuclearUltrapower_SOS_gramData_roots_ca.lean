-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_gramData_roots_ca
-- name    : OAI.NuclearUltrapower.SOS.gramData_roots_ca
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T16:22:02.55423+00:00
-- url     : https://prove2.me/theorems/be9ad757-4d4c-4d82-aa84-cf89b9ddc060
-- title:
--   OAI.NuclearUltrapower.SOS.gramData_roots_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`, with `open NuclearUltrapower.SL3Certificate`):
--
--   ```lean
--   theorem gramData_roots_ca : gramData = columns.map (fun q => columns.map (dot q))
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SL3Certificate.columns` and `OAI.NuclearUltrapower.SL3Certificate.dot` (definitions bundle `OAIQ229C004` of this split); `OAI.NuclearUltrapower.SOS.gramData` (definitions bundle `OAIQ229C015` of this split).
--
--   **Used by.** The proofs of `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate_ca` and `OAI_NuclearUltrapower_SOS_residual_value_generic_ca` of this split import it.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ229C015

section

attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
open NuclearUltrapower.SL3Certificate
theorem gramData_roots_ca : gramData = columns.map (fun q => columns.map (dot q)) := by
  sorry

end NuclearUltrapower.SOS
end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_LaughlinFock_collectedFourChecked_13_3
-- name    : OAI.LaughlinFock.collectedFourChecked_13_3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T22:35:10.098674+00:00
-- url     : https://prove2.me/theorems/b2afe535-b05e-4171-b30c-1d060d9d3c56
-- title:
--   OAI.LaughlinFock.collectedFourChecked_13_3: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LaughlinFock.collectedFourChecked_13_3` of [lean/OAI/Analysis/LaughlinFock/Sparse1308.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Sparse1308.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LaughlinFock`):
--
--   ```lean
--   theorem collectedFourChecked_13_3 : collectNumericRowParts 13 3 = collectedFourData_13_3
--   ```
--
--   **Definitions.** The statement is written with `OAI.LaughlinFock.CollectedFourTerm` and `OAI.LaughlinFock.collectNumericRowParts` (definitions bundle `OAIQ084L000` of this split); `OAI.LaughlinFock.collectedFourData_13_3` (definitions bundle `OAIQ084L022` of this split).
--
--   **Used by.** The proof of `OAI.LaughlinFock.collectedFourChecked_13` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Sparse1308.lean (declaration OAI.LaughlinFock.collectedFourChecked_13_3)

import Mathlib
import Definitions.Def_OAIQ084L022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LaughlinFock

theorem collectedFourChecked_13_3 : collectNumericRowParts 13 3 = collectedFourData_13_3 := by
  sorry

end LaughlinFock

end OAI
end

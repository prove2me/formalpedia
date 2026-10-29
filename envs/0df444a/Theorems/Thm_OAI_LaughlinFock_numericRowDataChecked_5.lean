-- Prove2me | Theorems.Thm_OAI_LaughlinFock_numericRowDataChecked_5
-- name    : OAI.LaughlinFock.numericRowDataChecked_5
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T22:33:05.975318+00:00
-- url     : https://prove2.me/theorems/9919d02a-3d82-4bd3-99a2-f218540e49bb
-- title:
--   OAI.LaughlinFock.numericRowDataChecked_5: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LaughlinFock.numericRowDataChecked_5` of [lean/OAI/Analysis/LaughlinFock/NumericTrace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/NumericTrace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LaughlinFock`, with `open scoped BigOperators Matrix ComplexOrder`):
--
--   ```lean
--   theorem numericRowDataChecked_5 :
--       rowEntryList_5.map (rowToNumeric ⟨5, by decide⟩) = numericRowData_5
--   ```
--
--   **Definitions.** The statement is written with `OAI.LaughlinFock.NumericRowEntry`, `OAI.LaughlinFock.RowEntry` and `OAI.LaughlinFock.numericRowData_5` (definitions bundle `OAIQ084L000` of this split); `OAI.LaughlinFock.rowEntryList_5` and `OAI.LaughlinFock.rowToNumeric` (definitions bundle `OAIQ084L015` of this split).
--
--   **Used by.** The proofs of `OAI.LaughlinFock.fourYChecked_12`, `OAI.LaughlinFock.fourYChecked_5`, `OAI.LaughlinFock.fourYChecked_7`, `OAI.LaughlinFock.integerRowsFourTrace_collected` and `OAI.LaughlinFock.integerRowsFourTrace_parts` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/NumericTrace.lean (declaration OAI.LaughlinFock.numericRowDataChecked_5)

import Mathlib
import Definitions.Def_OAIQ084L015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem numericRowDataChecked_5 :
    rowEntryList_5.map (rowToNumeric ⟨5, by decide⟩) = numericRowData_5 := by
  sorry

end LaughlinFock
end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_LaughlinFock_rowEntryChecked_4
-- name    : OAI.LaughlinFock.rowEntryChecked_4
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T22:34:19.957494+00:00
-- url     : https://prove2.me/theorems/924a9a70-2ebb-4b31-94fc-018c7a08cdf9
-- title:
--   OAI.LaughlinFock.rowEntryChecked_4: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LaughlinFock.rowEntryChecked_4` of [lean/OAI/Analysis/LaughlinFock/EntryEnumeration.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/EntryEnumeration.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LaughlinFock`, with `open scoped BigOperators Matrix ComplexOrder`):
--
--   ```lean
--   theorem rowEntryChecked_4 : (Finset.univ : Finset (RowEntry 4)) = rowEntryData_4
--   ```
--
--   **Definitions.** The statement is written with `OAI.LaughlinFock.RowEntry` (definitions bundle `OAIQ084L000` of this split); `OAI.LaughlinFock.rowEntryData_4` (definitions bundle `OAIQ084L015` of this split).
--
--   **Used by.** The proofs of `OAI.LaughlinFock.fourYChecked_12`, `OAI.LaughlinFock.fourYChecked_5`, `OAI.LaughlinFock.fourYChecked_7`, `OAI.LaughlinFock.integerRowsFourTrace_collected` and `OAI.LaughlinFock.integerRowsFourTrace_parts` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/EntryEnumeration.lean (declaration OAI.LaughlinFock.rowEntryChecked_4)

import Mathlib
import Definitions.Def_OAIQ084L015

section

attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem rowEntryChecked_4 : (Finset.univ : Finset (RowEntry 4)) = rowEntryData_4 := by
  sorry

end LaughlinFock
end

end OAI
end

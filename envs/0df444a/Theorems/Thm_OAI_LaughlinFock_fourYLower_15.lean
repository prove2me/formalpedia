-- Prove2me | Theorems.Thm_OAI_LaughlinFock_fourYLower_15
-- name    : OAI.LaughlinFock.fourYLower_15
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-28T18:23:50.998554+00:00
-- url     : https://prove2.me/theorems/ba6c4f4d-374c-4737-ba92-5c5357c940bf
-- title:
--   OAI.LaughlinFock.fourYLower_15: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LaughlinFock.fourYLower_15` of [lean/OAI/Analysis/LaughlinFock/Certificate15.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate15.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LaughlinFock`, with `open scoped BigOperators Matrix ComplexOrder`):
--
--   ```lean
--   theorem fourYLower_15 (r s : CopyLabel 15) (hrs : s.val.val ≤ r.val.val) :
--       integerRowsFourTrace 15 r s = fourYData_15 r s
--   ```
--
--   **Definitions.** The statement is written with `OAI.LaughlinFock.CopyLabel` (definitions bundle `OAIQ084L000` of this split); `OAI.LaughlinFock.fourYData_15` (definitions bundle `OAIQ084L029` of this split); `OAI.LaughlinFock.integerRowsFourTrace` (definitions bundle `OAIQ084L043` of this split).
--
--   **Used by.** The proof of `OAI.LaughlinFock.integer_certificate_15` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate15.lean (declaration OAI.LaughlinFock.fourYLower_15)

import Mathlib
import Definitions.Def_OAIQ084L029
import Definitions.Def_OAIQ084L043

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_15 (r s : CopyLabel 15) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 15 r s = fourYData_15 r s := by
  sorry

end LaughlinFock
end

end OAI
end

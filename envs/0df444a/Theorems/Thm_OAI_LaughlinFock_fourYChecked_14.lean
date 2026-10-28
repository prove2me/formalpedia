-- Prove2me | Theorems.Thm_OAI_LaughlinFock_fourYChecked_14
-- name    : OAI.LaughlinFock.fourYChecked_14
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-28T18:20:54.398059+00:00
-- url     : https://prove2.me/theorems/da0ab4a2-6760-4175-87de-5b7efcb435ca
-- title:
--   OAI.LaughlinFock.fourYChecked_14: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LaughlinFock.fourYChecked_14` of [lean/OAI/Analysis/LaughlinFock/Certificate14.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate14.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LaughlinFock`, with `open scoped BigOperators Matrix ComplexOrder`):
--
--   ```lean
--   theorem fourYChecked_14 (r s : CopyLabel 14) :
--       integerRowsFourTrace 14 r s = fourYData_14 r s
--   ```
--
--   **Definitions.** The statement is written with `OAI.LaughlinFock.CopyLabel` (definitions bundle `OAIQ084L000` of this split); `OAI.LaughlinFock.fourYData_14` (definitions bundle `OAIQ084L034` of this split); `OAI.LaughlinFock.integerRowsFourTrace` (definitions bundle `OAIQ084L043` of this split).
--
--   **Used by.** The proof of `OAI.LaughlinFock.integer_certificate_14` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate14.lean (declaration OAI.LaughlinFock.fourYChecked_14)

import Mathlib
import Definitions.Def_OAIQ084L034
import Definitions.Def_OAIQ084L043

section

attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYChecked_14 (r s : CopyLabel 14) :
    integerRowsFourTrace 14 r s = fourYData_14 r s := by
  sorry

end LaughlinFock
end

end OAI
end

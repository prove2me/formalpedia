-- Prove2me | Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_15_13
-- name    : OAI.LaughlinFock.fourYNumber_15_15_13
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T18:15:08.981355+00:00
-- url     : https://prove2.me/theorems/60d0d0d1-7a37-43c2-978b-2dfd25b37074
-- title:
--   OAI.LaughlinFock.fourYNumber_15_15_13: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LaughlinFock.fourYNumber_15_15_13` of [lean/OAI/Analysis/LaughlinFock/Certificate15Data.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate15Data.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LaughlinFock`, with `open scoped BigOperators Matrix ComplexOrder`):
--
--   ```lean
--   theorem fourYNumber_15_15_13 :
--       (collectedFourTrace 15 15 13 collectedFourData_15 : ℚ) / fourCommonDenominator = (131081604324030412414565143941/1342177280000000000000000)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LaughlinFock.fourCommonDenominator` (definitions bundle `OAIQ084L001` of this split); `OAI.LaughlinFock.collectedFourData_15` and `OAI.LaughlinFock.collectedFourTrace` (definitions bundle `OAIQ084L022` of this split).
--
--   **Used by.** The proof of `OAI.LaughlinFock.fourYLower_15` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate15Data.lean (declaration OAI.LaughlinFock.fourYNumber_15_15_13)

import Mathlib
import Definitions.Def_OAIQ084L022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYNumber_15_15_13 :
    (collectedFourTrace 15 15 13 collectedFourData_15 : ℚ) / fourCommonDenominator = (131081604324030412414565143941/1342177280000000000000000) := by
  sorry

end LaughlinFock
end

end OAI
end

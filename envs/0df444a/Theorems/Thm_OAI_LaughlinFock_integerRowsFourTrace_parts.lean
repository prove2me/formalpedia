-- Prove2me | Theorems.Thm_OAI_LaughlinFock_integerRowsFourTrace_parts
-- name    : OAI.LaughlinFock.integerRowsFourTrace_parts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T18:24:31.404815+00:00
-- url     : https://prove2.me/theorems/30a3d559-e285-47d8-b476-cfb1ba2926e3
-- title:
--   OAI.LaughlinFock.integerRowsFourTrace_parts: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LaughlinFock.integerRowsFourTrace_parts` of [lean/OAI/Analysis/LaughlinFock/PartsTrace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/PartsTrace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LaughlinFock`, with `open scoped BigOperators Matrix ComplexOrder`):
--
--   ```lean
--   theorem integerRowsFourTrace_parts {D : ℕ} (hD : D ≤ 23)
--       (ls : Fin 8 → List (List CollectedFourTerm))
--       (hls : ∀ t, collectNumericRowParts D t = ls t) (r s : CopyLabel D) :
--       integerRowsFourTrace D r s =
--         (collectedFourPartsTrace D r.val.val s.val.val ls : ℚ) / fourCommonDenominator
--   ```
--
--   **Definitions.** The statement is written with `OAI.LaughlinFock.CollectedFourTerm`, `OAI.LaughlinFock.CopyLabel` and `OAI.LaughlinFock.collectNumericRowParts` (definitions bundle `OAIQ084L000` of this split); `OAI.LaughlinFock.fourCommonDenominator` (definitions bundle `OAIQ084L001` of this split); `OAI.LaughlinFock.collectedFourPartsTrace` (definitions bundle `OAIQ084L009` of this split); `OAI.LaughlinFock.integerRowsFourTrace` (definitions bundle `OAIQ084L043` of this split).
--
--   **Used by.** The proofs of `OAI.LaughlinFock.fourYChecked_10`, `OAI.LaughlinFock.fourYChecked_11`, `OAI.LaughlinFock.fourYChecked_13`, `OAI.LaughlinFock.fourYChecked_14`, `OAI.LaughlinFock.fourYChecked_8` and `OAI.LaughlinFock.fourYLower_9` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/PartsTrace.lean (declaration OAI.LaughlinFock.integerRowsFourTrace_parts)

import Mathlib
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

theorem integerRowsFourTrace_parts {D : ℕ} (hD : D ≤ 23)
    (ls : Fin 8 → List (List CollectedFourTerm))
    (hls : ∀ t, collectNumericRowParts D t = ls t) (r s : CopyLabel D) :
    integerRowsFourTrace D r s =
      (collectedFourPartsTrace D r.val.val s.val.val ls : ℚ) / fourCommonDenominator := by
  sorry

end LaughlinFock
end

end OAI
end

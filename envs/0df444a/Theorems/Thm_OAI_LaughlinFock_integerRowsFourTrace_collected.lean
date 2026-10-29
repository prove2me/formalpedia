-- Prove2me | Theorems.Thm_OAI_LaughlinFock_integerRowsFourTrace_collected
-- name    : OAI.LaughlinFock.integerRowsFourTrace_collected
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T18:23:27.62118+00:00
-- url     : https://prove2.me/theorems/dac3bdac-93b6-47de-b192-013e821f236b
-- title:
--   OAI.LaughlinFock.integerRowsFourTrace_collected: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LaughlinFock.integerRowsFourTrace_collected` of [lean/OAI/Analysis/LaughlinFock/SparseTrace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/SparseTrace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LaughlinFock`, with `open scoped BigOperators Matrix ComplexOrder`):
--
--   ```lean
--   theorem integerRowsFourTrace_collected {D : ℕ} (hD : D ≤ 23) (ls : List CollectedFourTerm)
--       (hls : collectedFourTerms D = ls) (r s : CopyLabel D) :
--       integerRowsFourTrace D r s =
--         (collectedFourTrace D r.val.val s.val.val ls : ℚ) / fourCommonDenominator
--   ```
--
--   **Definitions.** The statement is written with `OAI.LaughlinFock.CollectedFourTerm` and `OAI.LaughlinFock.CopyLabel` (definitions bundle `OAIQ084L000` of this split); `OAI.LaughlinFock.fourCommonDenominator` (definitions bundle `OAIQ084L001` of this split); `OAI.LaughlinFock.collectedFourTerms` (definitions bundle `OAIQ084L011` of this split); `OAI.LaughlinFock.collectedFourTrace` (definitions bundle `OAIQ084L022` of this split); `OAI.LaughlinFock.integerRowsFourTrace` (definitions bundle `OAIQ084L043` of this split).
--
--   **Used by.** The proofs of `OAI.LaughlinFock.fourYChecked_16`, `OAI.LaughlinFock.fourYChecked_17`, `OAI.LaughlinFock.fourYChecked_19`, `OAI_LaughlinFock_fourYChecked_20`, `OAI_LaughlinFock_fourYChecked_21`, `OAI_LaughlinFock_fourYChecked_22`, `OAI.LaughlinFock.fourYChecked_23`, `OAI.LaughlinFock.fourYLower_15`, `OAI.LaughlinFock.integer_certificate_18`, `OAI.LaughlinFock.integer_certificate_20`, `OAI.LaughlinFock.integer_certificate_21` and `OAI.LaughlinFock.integer_certificate_22` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/SparseTrace.lean (declaration OAI.LaughlinFock.integerRowsFourTrace_collected)

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

theorem integerRowsFourTrace_collected {D : ℕ} (hD : D ≤ 23) (ls : List CollectedFourTerm)
    (hls : collectedFourTerms D = ls) (r s : CopyLabel D) :
    integerRowsFourTrace D r s =
      (collectedFourTrace D r.val.val s.val.val ls : ℚ) / fourCommonDenominator := by
  sorry

end LaughlinFock
end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate16_rows_checked
-- name    : OAI.LaughlinGap.RealOccupation.Certificate16.rows_checked
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:41:00.64595+00:00
-- url     : https://prove2.me/theorems/6b806923-0e10-45fa-9e18-109483e1cb94
-- title:
--   OAI.LaughlinGap.RealOccupation.Certificate16.rows_checked: intermediate lemma from OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LaughlinGap.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LaughlinGap.RealOccupation.Certificate16.rows_checked` of [lean/OAI/Analysis/LaughlinGap/Certificate16.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate16.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LaughlinGap.RealOccupation.Certificate16`, with `open scoped BigOperators ComplexOrder`, `open Spin`):
--
--   ```lean
--   lemma rows_checked (u v : Fin 8) : exactFourEval 16 (2*u.val+1) (2*v.val+1) = Y u v
--   ```
--
--   **Definitions.** The statement is written with `OAI.LaughlinGap.RealOccupation.Certificate16.Y` (definitions bundle `OAIQ030L003` of this split); `OAI.LaughlinGap.RealOccupation.exactFourEval` (definitions bundle `OAIQ030L028` of this split).
--
--   **Used by.** The proof of `OAI.LaughlinGap.RealOccupation.Certificate16.certificate` of this split imports it.
-- source:
--   OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate16.lean (declaration OAI.LaughlinGap.RealOccupation.Certificate16.rows_checked)

import Mathlib
import Definitions.Def_OAIQ030L003
import Definitions.Def_OAIQ030L028

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate16

lemma rows_checked (u v : Fin 8) : exactFourEval 16 (2*u.val+1) (2*v.val+1) = Y u v := by
  sorry
end Certificate16
end LaughlinGap.RealOccupation

end

end OAI
end

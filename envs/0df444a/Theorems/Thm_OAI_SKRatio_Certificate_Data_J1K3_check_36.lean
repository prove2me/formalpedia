-- Prove2me | Theorems.Thm_OAI_SKRatio_Certificate_Data_J1K3_check_36
-- name    : OAI.SKRatio.Certificate.Data.J1K3.check_36
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:35:09.989866+00:00
-- url     : https://prove2.me/theorems/ff35df44-b16f-40f1-b780-7c1eab124136
-- title:
--   OAI.SKRatio.Certificate.Data.J1K3.check_36: intermediate lemma from OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKRatio.Certificate.Data.J1K3.check_36` of [lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ1K3.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ1K3.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKRatio.Certificate.Data.J1K3`, with `open Real MeasureTheory`):
--
--   ```lean
--   lemma check_36 : expression.check (-10+(36:ℚ)*(5*(1/10))) (1/10) 5 (blocks 36) = true
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKRatio.Certificate.Data.J1K3.expression` (definitions bundle `OAIQ024S000` of this split); `OAI.SKRatio.Certificate.Data.J1K3.blocks` (definitions bundle `OAIQ024S004` of this split); `OAI.SKRatio.Certificate.Expr.check` (definitions bundle `OAIQ024S016` of this split).
--
--   **Used by.** The proof of `OAI.SKRatio.Certificate.Data.J1K3.checks` of this split imports it.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ1K3.lean (declaration OAI.SKRatio.Certificate.Data.J1K3.check_36)

import Mathlib
import Definitions.Def_OAIQ024S016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K3

lemma check_36 : expression.check (-10+(36:ℚ)*(5*(1/10))) (1/10) 5 (blocks 36) = true := by
  sorry

end SKRatio.Certificate.Data.J1K3

end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_SKRatio_Certificate_Data_J3K4_integral_bound
-- name    : OAI.SKRatio.Certificate.Data.J3K4.integral_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:24:40.730469+00:00
-- url     : https://prove2.me/theorems/e0444c79-a36c-4437-91c8-37b455b44929
-- title:
--   OAI.SKRatio.Certificate.Data.J3K4.integral_bound: intermediate lemma from OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKRatio.Certificate.Data.J3K4.integral_bound` of [lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ3K4.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ3K4.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKRatio.Certificate.Data.J3K4`, with `open Real MeasureTheory`):
--
--   ```lean
--   theorem integral_bound :
--       (∫ h, scalarFunction (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 4 h ∂Scalar.fieldLaw (19/40)) ∈ (⟨0,2401/62500⟩ : Box)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKRatio.Certificate.Box`, `OAI.SKRatio.Certificate.scalarFunction` and `OAI.SKRatio.Certificate.Box.instMembershipReal` (definitions bundle `OAIQ024S000` of this split); `OAI.SKRatio.Scalar.fieldLaw` (definitions bundle `OAIQ024S001` of this split).
--
--   **Used by.** The proof of `OAI.SKRatio.Certificate.uniform_slacks` of this split imports it.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ3K4.lean (declaration OAI.SKRatio.Certificate.Data.J3K4.integral_bound)

import Mathlib
import Definitions.Def_OAIQ024S000
import Definitions.Def_OAIQ024S001

section

attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K4

theorem integral_bound :
    (∫ h, scalarFunction (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 4 h ∂Scalar.fieldLaw (19/40)) ∈ (⟨0,2401/62500⟩ : Box) := by
  sorry

end SKRatio.Certificate.Data.J3K4

end

end OAI
end

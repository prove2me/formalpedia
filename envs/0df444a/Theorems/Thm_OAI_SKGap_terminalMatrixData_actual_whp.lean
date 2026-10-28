-- Prove2me | Theorems.Thm_OAI_SKGap_terminalMatrixData_actual_whp
-- name    : OAI.SKGap.terminalMatrixData_actual_whp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:25:23.836682+00:00
-- url     : https://prove2.me/theorems/2c97ff78-3aa1-44ef-bbee-94a886b3c6c8
-- title:
--   OAI.SKGap.terminalMatrixData_actual_whp: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.terminalMatrixData_actual_whp` of [lean/OAI/Probability/SKGap/Terminal/TerminalHighProbability.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Terminal/TerminalHighProbability.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open MeasureTheory ProbabilityTheory Real Set Filter`, `open scoped Topology`):
--
--   ```lean
--   lemma terminalMatrixData_actual_whp {β α ε l : ℝ} (hβ : 0 < β) (hα : 0 ≤ α)
--       (hε : 0 < ε) (hl : 0 ≤ l) (hedge : 2*sqrt (β^2*α) ≤ ε/6)
--       (h₅ : 0 < ε^2/(36*π^2*(β^2))-(l*α+log (1+exp (-l))))
--       (h₆ : 0 < ε/(4*(β^2))-(l*α+log (1+exp (-l))+α*log 2)) :
--       Tendsto (fun n : ℕ=>(disorderLaw β n).real {g | terminalMatrixData (terminalMatrixBound (β^2)) α ε g}) atTop (𝓝 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.terminalMatrixBound` and `OAI.SKGap.terminalMatrixData` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGap.Disorder`, `OAI.SKGap.Edge` and `OAI.SKGap.disorderLaw` (the published bundle `Def_SKHighTemperature`).
--
--   **Used by.** The proof of `OAI.SKGap.terminal_gap_high_probability` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Terminal/TerminalHighProbability.lean (declaration OAI.SKGap.terminalMatrixData_actual_whp)

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_OAIQ072A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology

lemma terminalMatrixData_actual_whp {β α ε l : ℝ} (hβ : 0 < β) (hα : 0 ≤ α)
    (hε : 0 < ε) (hl : 0 ≤ l) (hedge : 2*sqrt (β^2*α) ≤ ε/6)
    (h₅ : 0 < ε^2/(36*π^2*(β^2))-(l*α+log (1+exp (-l))))
    (h₆ : 0 < ε/(4*(β^2))-(l*α+log (1+exp (-l))+α*log 2)) :
    Tendsto (fun n : ℕ=>(disorderLaw β n).real {g | terminalMatrixData (terminalMatrixBound (β^2)) α ε g}) atTop (𝓝 1) := by
  sorry
end SKGap

end
end

end OAI
end

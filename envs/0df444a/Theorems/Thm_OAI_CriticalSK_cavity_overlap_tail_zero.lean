-- Prove2me | Theorems.Thm_OAI_CriticalSK_cavity_overlap_tail_zero
-- name    : OAI.CriticalSK.cavity_overlap_tail_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:31:43.670221+00:00
-- url     : https://prove2.me/theorems/23094b9f-bb90-42b7-a0ad-d003f4836fe4
-- title:
--   OAI.CriticalSK.cavity_overlap_tail_zero: intermediate lemma from OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.covariance_and_linear_tests` and `OAI.CriticalSK.critical_mixing_lower_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical slowing down in the Sherrington–Kirkpatrick model*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalSK.cavity_overlap_tail_zero` of [lean/OAI/MathematicalPhysics/CriticalSK/Rayleigh.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/Rayleigh.lean) at commit adc7f12, ported to this platform's Lean and Mathlib.
--
--   **The statement**, as published (namespace `OAI.CriticalSK`, with `open scoped BigOperators Topology NNReal ENNReal`, `open Set Filter MeasureTheory`):
--
--   ```lean
--   lemma cavity_overlap_tail_zero : Tendsto (fun n : ℕ => (disorderLaw (n+4)).real
--       {W | (n+4:ℝ)^(-3/5:ℝ) ≤ gibbsOverlap W}) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalSK.gibbsOverlap` (definitions bundle `OAIQWCSK001` of this split); `OAI.CriticalSK.Disorder`, `OAI.CriticalSK.Edge` and `OAI.CriticalSK.disorderLaw` (the published bundle `Def_CriticalSK`).
--
--   **Used by.** The proof of `OAI.CriticalSK.covariance_and_linear_tests` of this split imports it.
-- source:
--   OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/Rayleigh.lean (declaration OAI.CriticalSK.cavity_overlap_tail_zero)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_OAIQWCSK001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

open Set Filter MeasureTheory

lemma cavity_overlap_tail_zero : Tendsto (fun n : ℕ => (disorderLaw (n+4)).real
    {W | (n+4:ℝ)^(-3/5:ℝ) ≤ gibbsOverlap W}) atTop (𝓝 0) := by
  sorry

end CriticalSK

end

end OAI
end

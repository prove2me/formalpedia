-- Prove2me | Theorems.Thm_OAI_CriticalSK_covariance_upper_tight
-- name    : OAI.CriticalSK.covariance_upper_tight
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:29:42.734784+00:00
-- url     : https://prove2.me/theorems/16533f64-7db4-4272-b5ff-84e8eae7f300
-- title:
--   OAI.CriticalSK.covariance_upper_tight: intermediate lemma from OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.covariance_and_linear_tests` and `OAI.CriticalSK.critical_mixing_lower_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical slowing down in the Sherrington–Kirkpatrick model*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalSK.covariance_upper_tight` of [lean/OAI/MathematicalPhysics/CriticalSK/Covariance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/Covariance.lean) at commit adc7f12, ported to this platform's Lean and Mathlib.
--
--   **The statement**, as published (namespace `OAI.CriticalSK`, with `open scoped BigOperators Topology NNReal ENNReal`, `open Set MeasureTheory`, `open Set MeasureTheory Filter`):
--
--   ```lean
--   lemma covariance_upper_tight {α : ℝ} (hα : 0 < α) :
--       ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (disorderLaw (n+4)).real
--         {W | C*(n+4:ℝ)^(2/3:ℝ) ≤ covarianceNorm W} < α
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalSK.Disorder`, `OAI.CriticalSK.Edge`, `OAI.CriticalSK.covarianceNorm` and `OAI.CriticalSK.disorderLaw` (the published bundle `Def_CriticalSK`).
--
--   **Used by.** The proof of `OAI.CriticalSK.covariance_and_linear_tests` of this split imports it.
-- source:
--   OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/Covariance.lean (declaration OAI.CriticalSK.covariance_upper_tight)

import Mathlib
import Definitions.Def_CriticalSK

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

open Set MeasureTheory

open Set MeasureTheory Filter

lemma covariance_upper_tight {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (disorderLaw (n+4)).real
      {W | C*(n+4:ℝ)^(2/3:ℝ) ≤ covarianceNorm W} < α := by
  sorry

end CriticalSK

end

end OAI
end

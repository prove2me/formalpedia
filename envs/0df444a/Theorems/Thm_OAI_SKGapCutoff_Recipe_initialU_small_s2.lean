-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_initialU_small_s2
-- name    : OAI.SKGapCutoff.Recipe.initialU_small_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:52:25.242439+00:00
-- url     : https://prove2.me/theorems/72156c3b-e8e8-4304-bdb2-db192c3306ff
-- title:
--   OAI.SKGapCutoff.Recipe.initialU_small_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators Matrix.Norms.Frobenius`, `open SKGap.Stein Primary SKGap.ImplicitSystem`):
--
--   ```lean
--   lemma initialU_small_s2 (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
--       (r e : Fin n→ℝ) (x : Spin n) {T : ℝ} (hT : 0≤T) (he : vectorNorm e≤1)
--       (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T) :
--       SmallBound (initialU f z a r e) x (ratioSmallBudget (.kernel f) T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.opNorm`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.VectorFields`, `OAI.SKGap.Stein.KernelExpr`, `OAI.SKGapCutoff.Primary.derivativeMatrix`, `OAI.SKGapCutoff.Primary.derivativeVector`, `OAI.SKGapCutoff.Recipe.SmallBound`, `OAI.SKGapCutoff.Recipe.vectorNorm` and `OAI.SKGap.Stein.RatioExpr` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.initialU` and `OAI.SKGapCutoff.Recipe.ratioSmallBudget` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ072A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem
variable {n : ℕ}

lemma initialU_small_s2 (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r e : Fin n→ℝ) (x : Spin n) {T : ℝ} (hT : 0≤T) (he : vectorNorm e≤1)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T) :
    SmallBound (initialU f z a r e) x (ratioSmallBudget (.kernel f) T) := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end

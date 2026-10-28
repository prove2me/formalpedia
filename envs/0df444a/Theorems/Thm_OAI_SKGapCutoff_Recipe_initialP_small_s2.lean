-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_initialP_small_s2
-- name    : OAI.SKGapCutoff.Recipe.initialP_small_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:52:25.719713+00:00
-- url     : https://prove2.me/theorems/ea501f17-c33b-4525-bad0-973306ea970f
-- title:
--   OAI.SKGapCutoff.Recipe.initialP_small_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators Matrix.Norms.Frobenius`, `open SKGap.Stein Primary SKGap.ImplicitSystem`):
--
--   ```lean
--   lemma initialP_small_s2 (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
--       (r e : Fin n→ℝ) (x : Spin n) {R T : ℝ} (hT : 0≤T) (he : vectorNorm e≤1)
--       (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
--       (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T) :
--       SmallBound (initialP f z a r e) x
--         (ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.opNorm`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.VectorFields`, `OAI.SKGapCutoff.flip`, `OAI.SKGap.Stein.KernelExpr`, `OAI.SKGapCutoff.Primary.derivativeMatrix`, `OAI.SKGapCutoff.Primary.derivativeVector`, `OAI.SKGapCutoff.Recipe.SmallBound`, `OAI.SKGapCutoff.Recipe.vectorNorm`, `OAI.SKGap.Stein.Axis`, `OAI.SKGap.Stein.RatioExpr.d` and `OAI.SKGap.Stein.RatioExpr` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.initialP`, `OAI.SKGapCutoff.Recipe.kernelSmallBudget`, `OAI.SKGapCutoff.Recipe.phiExpr` and `OAI.SKGapCutoff.Recipe.ratioSmallBudget` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** The proof of `OAI.SKGapCutoff.Recipe.literalInitial_partial_small_s2` of this split imports it.
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

lemma initialP_small_s2 (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r e : Fin n→ℝ) (x : Spin n) {R T : ℝ} (hT : 0≤T) (he : vectorNorm e≤1)
    (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T) :
    SmallBound (initialP f z a r e) x
      (ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T) := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end

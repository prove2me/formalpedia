-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_literalInitial_partial_small_s2
-- name    : OAI.SKGapCutoff.Recipe.literalInitial_partial_small_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:52:24.054884+00:00
-- url     : https://prove2.me/theorems/cb98fb3e-48eb-4989-9aab-1b84920292d0
-- title:
--   OAI.SKGapCutoff.Recipe.literalInitial_partial_small_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators Matrix.Norms.Frobenius`, `open SKGap.Stein Primary`):
--
--   ```lean
--   lemma literalInitial_partial_small_s2 (J : Interaction n) (j d : ℝ) (f : KernelExpr)
--       (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
--       (hd : d≠0) {R T B : ℝ} (hT : 0≤T) (he : vectorNorm e≤1)
--       (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
--       (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T)
--       (hW : SmallBound w x B)
--       (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x)
--       (hwf : ∀k,w (flip x k)=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) (flip x k)) :
--       SmallBound ((literalInitial J j d f z m a c r e).implicitPartial y) x
--         (B*ratioSmallBudget (.kernel phiExpr.dz) T+
--           ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.opNorm`, `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.VectorFields`, `OAI.SKGapCutoff.flip`, `OAI.SKGap.Stein.KernelExpr`, `OAI.SKGapCutoff.Primary.derivativeMatrix`, `OAI.SKGapCutoff.Primary.derivativeVector`, `OAI.SKGapCutoff.Recipe.SmallBound`, `OAI.SKGapCutoff.Recipe.vectorNorm`, `OAI.SKGap.Stein.Axis`, `OAI.SKGap.Stein.KernelExpr.dz`, `OAI.SKGap.Stein.RatioExpr.d`, `OAI.SKGap.Stein.RatioExpr` and `OAI.SKGapCutoff.Recipe.OrdinaryData.sourceOf` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.kernelSmallBudget`, `OAI.SKGapCutoff.Recipe.literalInitial`, `OAI.SKGapCutoff.Recipe.phiExpr`, `OAI.SKGapCutoff.Recipe.ratioSmallBudget` and `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitPartial` (definitions bundle `OAIQ072A002` of this split).
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
open SKGap.Stein Primary
variable {n : ℕ}

lemma literalInitial_partial_small_s2 (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (hd : d≠0) {R T B : ℝ} (hT : 0≤T) (he : vectorNorm e≤1)
    (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T)
    (hW : SmallBound w x B)
    (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x)
    (hwf : ∀k,w (flip x k)=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) (flip x k)) :
    SmallBound ((literalInitial J j d f z m a c r e).implicitPartial y) x
      (B*ratioSmallBudget (.kernel phiExpr.dz) T+
        ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T) := by
  sorry
end SKGapCutoff.Recipe

end
end

end OAI
end

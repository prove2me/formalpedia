-- Prove2me | Theorems.Thm_OAI_RadialTransition_finiteGrandPressure_family_box_error_rt2
-- name    : OAI.RadialTransition.finiteGrandPressure_family_box_error_rt2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T22:36:09.307867+00:00
-- url     : https://prove2.me/theorems/0d7e9165-19f0-4feb-a072-54c4c714393b
-- title:
--   OAI.RadialTransition.finiteGrandPressure_family_box_error_rt2: intermediate lemma from OpenAI, A radial continuum phase transition with algebraic decay
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RadialTransition.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A radial continuum phase transition with algebraic decay*, OpenAI Math Release, September 24, 2026, result family 228, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RadialTransition.finiteGrandPressure_family_box_error` of [lean/OAI/Probability/RadialTransition/RangeBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/RangeBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RadialTransition`, with `open Function MeasureTheory Set Filter`, `open scoped ContDiff NNReal BigOperators ENNReal`):
--
--   ```lean
--   theorem finiteGrandPressure_family_box_error_rt2 {q : ℕ} (hq : 0 < q)
--       {t β h R₀ : ℝ} {a R : ℕ → ℝ} (ht : 1 ≤ t) (hβ : 0 < β)
--       (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
--       (hR₀ : 2 ≤ R₀) (hrange : ∀ n, R n ≤ R₀)
--       (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, a n) ≤ (t^2/8)/8) :
--       |finiteGrandPressure (familyPotential t a R) t ((q:ℝ)/4) β h-
--         grandPressure (familyPotential t a R) t β h| ≤
--         boxPressureConstant t β h (∑' n, a n)*R₀/((q:ℝ)/4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RadialTransition.boxPressureConstant`, `OAI.RadialTransition.bumpIntegral`, `OAI.RadialTransition.familyPotential`, `OAI.RadialTransition.finiteGrandPressure` and `OAI.RadialTransition.grandPressure` (definitions bundle `OAIQ112R000` of this split).
--
--   **Used by.** The proof of `OAI.RadialTransition.family_kac_variational_grid_rt2` of this split imports it.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/RangeBounds.lean (declaration OAI.RadialTransition.finiteGrandPressure_family_box_error)

import Mathlib
import Definitions.Def_OAIQ112R000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uI

noncomputable section

open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

theorem finiteGrandPressure_family_box_error_rt2 {q : ℕ} (hq : 0 < q)
    {t β h R₀ : ℝ} {a R : ℕ → ℝ} (ht : 1 ≤ t) (hβ : 0 < β)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, R n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, a n) ≤ (t^2/8)/8) :
    |finiteGrandPressure (familyPotential t a R) t ((q:ℝ)/4) β h-
      grandPressure (familyPotential t a R) t β h| ≤
      boxPressureConstant t β h (∑' n, a n)*R₀/((q:ℝ)/4) := by
  sorry

end RadialTransition

end

end OAI
end

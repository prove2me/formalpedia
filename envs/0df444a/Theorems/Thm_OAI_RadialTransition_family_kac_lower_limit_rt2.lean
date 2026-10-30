-- Prove2me | Theorems.Thm_OAI_RadialTransition_family_kac_lower_limit_rt2
-- name    : OAI.RadialTransition.family_kac_lower_limit_rt2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T22:35:15.919731+00:00
-- url     : https://prove2.me/theorems/0f402f6c-47ab-4eaa-9bad-ddb940eeab87
-- title:
--   OAI.RadialTransition.family_kac_lower_limit_rt2: intermediate lemma from OpenAI, A radial continuum phase transition with algebraic decay
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RadialTransition.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A radial continuum phase transition with algebraic decay*, OpenAI Math Release, September 24, 2026, result family 228, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RadialTransition.family_kac_lower_limit` of [lean/OAI/Probability/RadialTransition/KacComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/KacComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RadialTransition`, with `open scoped BigOperators ENNReal NNReal`, `open MeasureTheory Set Filter`):
--
--   ```lean
--   lemma family_kac_lower_limit_rt2 {q : ℕ} (hq : 0 < q) {t β h R₀ a R D u : ℝ} {b S : ℕ → ℝ}
--       (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : (q:ℝ)/4 ≤ R) (hq1 : 1 ≤ (q:ℝ)/4)
--       (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
--       (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
--       (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8)
--       (hks : Summable (kacSeries (familyPotential t b S) q R t a β h))
--       (hD : Real.exp (β*(t^2/2)+t*(h+β*a*u)+1) ≤ D) :
--       finiteGrandPressure (familyPotential t b S) t ((q:ℝ)/4) β (h+β*a*u)-β*a/2*u^2 ≤
--         grandPressure (familyPotential t (prepend a b) (prepend R S)) t β h+
--         boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4)+
--         β*a/2*kernelRowError q R*D^2+Real.log ((D+2)*((q:ℝ)/4)^3)/(t*((q:ℝ)/4)^3)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RadialTransition.boxPressureConstant`, `OAI.RadialTransition.bumpIntegral`, `OAI.RadialTransition.familyPotential`, `OAI.RadialTransition.finiteGrandPressure`, `OAI.RadialTransition.grandPressure`, `OAI.RadialTransition.kacSeries`, `OAI.RadialTransition.kernelRowError` and `OAI.RadialTransition.prepend` (definitions bundle `OAIQ112R000` of this split).
--
--   **Used by.** The proof of `OAI.RadialTransition.family_kac_variational_grid_rt2` of this split imports it.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/KacComparison.lean (declaration OAI.RadialTransition.family_kac_lower_limit)

import Mathlib
import Definitions.Def_OAIQ112R000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma family_kac_lower_limit_rt2 {q : ℕ} (hq : 0 < q) {t β h R₀ a R D u : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : (q:ℝ)/4 ≤ R) (hq1 : 1 ≤ (q:ℝ)/4)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8)
    (hks : Summable (kacSeries (familyPotential t b S) q R t a β h))
    (hD : Real.exp (β*(t^2/2)+t*(h+β*a*u)+1) ≤ D) :
    finiteGrandPressure (familyPotential t b S) t ((q:ℝ)/4) β (h+β*a*u)-β*a/2*u^2 ≤
      grandPressure (familyPotential t (prepend a b) (prepend R S)) t β h+
      boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4)+
      β*a/2*kernelRowError q R*D^2+Real.log ((D+2)*((q:ℝ)/4)^3)/(t*((q:ℝ)/4)^3) := by
  sorry

end RadialTransition
end

end OAI
end

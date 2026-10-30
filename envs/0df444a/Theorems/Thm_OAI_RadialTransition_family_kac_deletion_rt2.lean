-- Prove2me | Theorems.Thm_OAI_RadialTransition_family_kac_deletion_rt2
-- name    : OAI.RadialTransition.family_kac_deletion_rt2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T22:35:28.676646+00:00
-- url     : https://prove2.me/theorems/84ff04eb-d9e8-4f10-b98b-f8fd30d309f9
-- title:
--   OAI.RadialTransition.family_kac_deletion_rt2: intermediate lemma from OpenAI, A radial continuum phase transition with algebraic decay
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RadialTransition.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A radial continuum phase transition with algebraic decay*, OpenAI Math Release, September 24, 2026, result family 228, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RadialTransition.family_kac_deletion` of [lean/OAI/Probability/RadialTransition/KacDeletion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/KacDeletion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RadialTransition`, with `open scoped BigOperators ENNReal NNReal`, `open MeasureTheory Set Filter`):
--
--   ```lean
--   lemma family_kac_deletion_rt2 {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
--       {t β h R₀ a R : ℝ} {b S : ℕ → ℝ} (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : 1 ≤ R)
--       (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
--       (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
--       (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8) :
--       |finiteGrandPressure (familyPotential t (prepend a b) (prepend R S)) t ((m:ℝ)*q/4) β h-
--         deletedKacPressure (familyPotential t b S) m q R t a β h| ≤
--         boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RadialTransition.boxPressureConstant`, `OAI.RadialTransition.bumpIntegral`, `OAI.RadialTransition.deletedKacPressure`, `OAI.RadialTransition.familyPotential`, `OAI.RadialTransition.finiteGrandPressure` and `OAI.RadialTransition.prepend` (definitions bundle `OAIQ112R000` of this split).
--
--   **Used by.** The proofs of `OAI.RadialTransition.family_kac_lower_limit_rt2` and `OAI.RadialTransition.family_kac_upper_limit_rt2` of this split import it.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/KacDeletion.lean (declaration OAI.RadialTransition.family_kac_deletion)

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

lemma family_kac_deletion_rt2 {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    {t β h R₀ a R : ℝ} {b S : ℕ → ℝ} (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : 1 ≤ R)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8) :
    |finiteGrandPressure (familyPotential t (prepend a b) (prepend R S)) t ((m:ℝ)*q/4) β h-
      deletedKacPressure (familyPotential t b S) m q R t a β h| ≤
      boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4) := by
  sorry

end RadialTransition
end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_RadialTransition_family_ideal_exists_active_rt2
-- name    : OAI.RadialTransition.family_ideal_exists_active_rt2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T22:35:05.834078+00:00
-- url     : https://prove2.me/theorems/cfc8f386-324c-47a3-92fa-2f4e9e26da40
-- title:
--   OAI.RadialTransition.family_ideal_exists_active_rt2: intermediate lemma from OpenAI, A radial continuum phase transition with algebraic decay
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RadialTransition.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A radial continuum phase transition with algebraic decay*, OpenAI Math Release, September 24, 2026, result family 228, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RadialTransition.family_ideal_exists_active` of [lean/OAI/Probability/RadialTransition/FamilyIdeal.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/FamilyIdeal.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RadialTransition`, with `open scoped BigOperators ENNReal NNReal`, `open MeasureTheory Set Filter`):
--
--   ```lean
--   lemma family_ideal_exists_active_rt2 {t β a h U κ : ℝ} {b S : ℕ → ℝ}
--       (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a)
--       (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
--       (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, b n) ≤ (t^2/8)/8)
--       (hκ : 0 < κ) (hc : κ ≤ β*t/3456-β*a/2) (hU : 1 ≤ U)
--       (hcut : h+β*t/2+1/t+1 ≤ κ*U) :
--       ∃ u ∈ Icc (0:ℝ) U, ActiveShift (grandPressure (familyPotential t b S) t) a β h u
--   ```
--
--   **Definitions.** The statement is written with `OAI.RadialTransition.ActiveShift`, `OAI.RadialTransition.bumpIntegral`, `OAI.RadialTransition.familyPotential` and `OAI.RadialTransition.grandPressure` (definitions bundle `OAIQ112R000` of this split).
--
--   **Used by.** The proofs of `OAI.RadialTransition.family_controls_rt2`, `OAI.RadialTransition.family_kac_variational_grid_rt2` and `OAI.RadialTransition.initial_separation_rt2` of this split import it.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/FamilyIdeal.lean (declaration OAI.RadialTransition.family_ideal_exists_active)

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

lemma family_ideal_exists_active_rt2 {t β a h U κ : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, b n) ≤ (t^2/8)/8)
    (hκ : 0 < κ) (hc : κ ≤ β*t/3456-β*a/2) (hU : 1 ≤ U)
    (hcut : h+β*t/2+1/t+1 ≤ κ*U) :
    ∃ u ∈ Icc (0:ℝ) U, ActiveShift (grandPressure (familyPotential t b S) t) a β h u := by
  sorry

end RadialTransition
end

end OAI
end

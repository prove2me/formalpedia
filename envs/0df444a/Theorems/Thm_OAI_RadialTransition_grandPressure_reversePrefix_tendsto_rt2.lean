-- Prove2me | Theorems.Thm_OAI_RadialTransition_grandPressure_reversePrefix_tendsto_rt2
-- name    : OAI.RadialTransition.grandPressure_reversePrefix_tendsto_rt2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T22:36:16.427469+00:00
-- url     : https://prove2.me/theorems/7aa15104-a598-48c6-924b-900509df550f
-- title:
--   OAI.RadialTransition.grandPressure_reversePrefix_tendsto_rt2: intermediate lemma from OpenAI, A radial continuum phase transition with algebraic decay
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RadialTransition.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A radial continuum phase transition with algebraic decay*, OpenAI Math Release, September 24, 2026, result family 228, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RadialTransition.grandPressure_reversePrefix_tendsto` of [lean/OAI/Probability/RadialTransition/TruncatedFamily.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/TruncatedFamily.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RadialTransition`, with `open scoped BigOperators NNReal`, `open Set Filter`):
--
--   ```lean
--   lemma grandPressure_reversePrefix_tendsto_rt2 {t A β h : ℝ} {a R : ℕ → ℝ}
--       (ht : 1 ≤ t) (hβ : 0 < β) (had : AdmissibleFamily t A a R)
--       (hrow : 2197*t*bumpIntegral⁻¹*A ≤ (t^2/8)/8) :
--       Tendsto (fun n => grandPressure (familyPotential t (reversePrefix 0 a n) (reversePrefix 1 R n)) t β h)
--         atTop (nhds (grandPressure (familyPotential t a R) t β h))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RadialTransition.AdmissibleFamily`, `OAI.RadialTransition.bumpIntegral`, `OAI.RadialTransition.familyPotential`, `OAI.RadialTransition.grandPressure` and `OAI.RadialTransition.reversePrefix` (definitions bundle `OAIQ112R000` of this split).
--
--   **Used by.** The proof of `OAI.RadialTransition.exists_family_pressure_ball_rt2` of this split imports it.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/TruncatedFamily.lean (declaration OAI.RadialTransition.grandPressure_reversePrefix_tendsto)

import Mathlib
import Definitions.Def_OAIQ112R000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal
open Set Filter
namespace RadialTransition

lemma grandPressure_reversePrefix_tendsto_rt2 {t A β h : ℝ} {a R : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (had : AdmissibleFamily t A a R)
    (hrow : 2197*t*bumpIntegral⁻¹*A ≤ (t^2/8)/8) :
    Tendsto (fun n => grandPressure (familyPotential t (reversePrefix 0 a n) (reversePrefix 1 R n)) t β h)
      atTop (nhds (grandPressure (familyPotential t a R) t β h)) := by
  sorry

end RadialTransition
end

end OAI
end

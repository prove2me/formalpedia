-- Prove2me | Theorems.Thm_OAI_RadialTransition_admissible_pressure_convex_rt2
-- name    : OAI.RadialTransition.admissible_pressure_convex_rt2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T22:34:14.945865+00:00
-- url     : https://prove2.me/theorems/dbda36ed-53d1-449a-9c79-0b009efb650b
-- title:
--   OAI.RadialTransition.admissible_pressure_convex_rt2: intermediate lemma from OpenAI, A radial continuum phase transition with algebraic decay
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RadialTransition.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A radial continuum phase transition with algebraic decay*, OpenAI Math Release, September 24, 2026, result family 228, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RadialTransition.admissible_pressure_convex` of [lean/OAI/Probability/RadialTransition/FamilyControls.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/FamilyControls.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RadialTransition`, with `open scoped BigOperators ENNReal NNReal`, `open MeasureTheory Set Filter`):
--
--   ```lean
--   lemma admissible_pressure_convex_rt2 {t A : ℝ} {b S : ℕ → ℝ}
--       (ht : 1 ≤ t) (had : AdmissibleFamily t A b S)
--       (hrow : 2197*t*bumpIntegral⁻¹*A ≤ (t^2/8)/8) :
--       ConvexOn ℝ positiveParameters (onParameters (grandPressure (familyPotential t b S) t))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RadialTransition.AdmissibleFamily`, `OAI.RadialTransition.Parameter`, `OAI.RadialTransition.bumpIntegral`, `OAI.RadialTransition.familyPotential`, `OAI.RadialTransition.grandPressure`, `OAI.RadialTransition.onParameters` and `OAI.RadialTransition.positiveParameters` (definitions bundle `OAIQ112R000` of this split).
--
--   **Used by.** The proofs of `OAI.RadialTransition.exists_family_pressure_ball_rt2` and `OAI.RadialTransition.family_controls_rt2` of this split import it.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/FamilyControls.lean (declaration OAI.RadialTransition.admissible_pressure_convex)

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

lemma admissible_pressure_convex_rt2 {t A : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (had : AdmissibleFamily t A b S)
    (hrow : 2197*t*bumpIntegral⁻¹*A ≤ (t^2/8)/8) :
    ConvexOn ℝ positiveParameters (onParameters (grandPressure (familyPotential t b S) t)) := by
  sorry

end RadialTransition
end

end OAI
end

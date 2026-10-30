-- Prove2me | Theorems.Thm_OAI_RadialTransition_exists_family_pressure_ball_rt2
-- name    : OAI.RadialTransition.exists_family_pressure_ball_rt2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T22:34:26.843086+00:00
-- url     : https://prove2.me/theorems/24a5969c-b497-43d9-a73c-693c964a9972
-- title:
--   OAI.RadialTransition.exists_family_pressure_ball_rt2: intermediate lemma from OpenAI, A radial continuum phase transition with algebraic decay
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RadialTransition.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A radial continuum phase transition with algebraic decay*, OpenAI Math Release, September 24, 2026, result family 228, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RadialTransition.exists_family_pressure_ball` of [lean/OAI/Probability/RadialTransition/InfiniteBall.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/InfiniteBall.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RadialTransition`, with `open scoped BigOperators NNReal`, `open Set Filter`):
--
--   ```lean
--   lemma exists_family_pressure_ball_rt2 :
--       ∃ t b : ℝ, 1 ≤ t ∧ 2 ≤ b ∧
--         2197*t*bumpIntegral⁻¹*iterationBudget ≤ (t^2/8)/8 ∧
--         ∃ x ∈ phaseWindow (1/8), Metric.closedBall targetSlope pressureRadius ⊆
--           supportSet (onParameters (grandPressure (familyPotential t (iterationMass b) (scaleRange b)) t)) positiveParameters x
--   ```
--
--   **Definitions.** The statement is written with `OAI.RadialTransition.Parameter`, `OAI.RadialTransition.bumpIntegral`, `OAI.RadialTransition.familyPotential`, `OAI.RadialTransition.grandPressure`, `OAI.RadialTransition.iterationBudget`, `OAI.RadialTransition.iterationMass`, `OAI.RadialTransition.onParameters`, `OAI.RadialTransition.phaseWindow`, `OAI.RadialTransition.positiveParameters`, `OAI.RadialTransition.pressureRadius`, `OAI.RadialTransition.scaleRange`, `OAI.RadialTransition.supportSet` and `OAI.RadialTransition.targetSlope` (definitions bundle `OAIQ112R000` of this split).
--
--   **Used by.** The proof of `OAI.RadialTransition.main` of this split imports it.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/InfiniteBall.lean (declaration OAI.RadialTransition.exists_family_pressure_ball)

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

lemma exists_family_pressure_ball_rt2 :
    ∃ t b : ℝ, 1 ≤ t ∧ 2 ≤ b ∧
      2197*t*bumpIntegral⁻¹*iterationBudget ≤ (t^2/8)/8 ∧
      ∃ x ∈ phaseWindow (1/8), Metric.closedBall targetSlope pressureRadius ⊆
        supportSet (onParameters (grandPressure (familyPotential t (iterationMass b) (scaleRange b)) t)) positiveParameters x := by
  sorry

end RadialTransition
end

end OAI
end

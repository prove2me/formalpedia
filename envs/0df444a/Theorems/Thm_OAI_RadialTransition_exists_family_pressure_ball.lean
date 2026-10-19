-- Prove2me | Theorems.Thm_OAI_RadialTransition_exists_family_pressure_ball
-- name    : OAI.RadialTransition.exists_family_pressure_ball
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:04:53.771518+00:00
-- url     : https://prove2.me/theorems/cd15cc4b-2586-459a-b37a-551b36c4fa3f
-- title:
--   Some admissible scale family has a full ball of supporting slopes for its grand pressure (OpenAI, radial phase transition)
-- statement:
--   There exist reals $t \ge 1$ and $b \ge 2$ with the following properties.
--   - They satisfy the row condition $2197\, t\, I^{-1}\cdot$ `iterationBudget` $\le t^2/64$.
--   - Let $P$ = `grandPressure (familyPotential t (iterationMass b) (scaleRange b)) t` be the grand pressure of the family potential with masses `iterationMass b` and doubly exponential ranges `scaleRange b`. Then there is a parameter $x \in$ `phaseWindow (1/8)` at which every slope in the closed ball of radius `pressureRadius` about `targetSlope` supports $P$ over $\{\beta > 0\}$.
--
--   The named functions come from the definitions bundle `OAIQWRTD000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.RadialTransition.exists_family_pressure_ball`, OpenAI's lemma of that name in `lean/OAI/Probability/RadialTransition/InfiniteBall.lean`.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/InfiniteBall.lean (declaration OAI.RadialTransition.exists_family_pressure_ball)

import Mathlib
import Definitions.Def_OAIQWRTD000

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

lemma exists_family_pressure_ball :
    ∃ t b : ℝ, 1 ≤ t ∧ 2 ≤ b ∧
      2197*t*bumpIntegral⁻¹*iterationBudget ≤ (t^2/8)/8 ∧
      ∃ x ∈ phaseWindow (1/8), Metric.closedBall targetSlope pressureRadius ⊆
        supportSet (onParameters (grandPressure (familyPotential t (iterationMass b) (scaleRange b)) t)) positiveParameters x := by
  sorry

end RadialTransition
end

end OAI
end

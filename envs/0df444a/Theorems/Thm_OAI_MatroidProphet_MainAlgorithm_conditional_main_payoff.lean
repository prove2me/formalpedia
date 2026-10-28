-- Prove2me | Theorems.Thm_OAI_MatroidProphet_MainAlgorithm_conditional_main_payoff
-- name    : OAI.MatroidProphet.MainAlgorithm.conditional_main_payoff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:28:26.232333+00:00
-- url     : https://prove2.me/theorems/246b1b95-0569-4d92-9a86-b68b5eefea28
-- title:
--   OAI.MatroidProphet.MainAlgorithm.conditional_main_payoff: intermediate lemma from OpenAI, One-sample matroid prophet inequalities against an almighty adversary
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatroidProphet.Assigned.secretary`, `OAI.MatroidProphet.Assigned.one_sample` and `OAI.MatroidProphet.Assigned.hidden_vector`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *One-sample matroid prophet inequalities against an almighty adversary*, OpenAI Math Release, September 23, 2026, result family 111, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatroidProphet.MainAlgorithm.conditional_main_payoff` of [lean/OAI/Probability/MatroidProphet/Algorithm/WeightedPayoff.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/MatroidProphet/Algorithm/WeightedPayoff.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatroidProphet.MainAlgorithm`, with `open Finset`):
--
--   ```lean
--   theorem conditional_main_payoff (M : Matroid (Fin n)) (hE : M.E = Set.univ)
--       (d : MainMasks n) (w : Fin n → Option ℤ) :
--       thinningRate / (2 * densityThreshold) *
--         (retainedFraction * analyzedComparisonMass M w d.H - ((2:ℝ)^21)⁻¹ *
--           ∑ e ∈ candidateLabels M w d.H, levelWeight weightBase (w e)) ≤
--         mainMean d (fun d' => mainWorstRounded M hE d' w)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatroidProphet.MainMasks`, `OAI.MatroidProphet.densityThreshold`, `OAI.MatroidProphet.levelWeight`, `OAI.MatroidProphet.retainedFraction`, `OAI.MatroidProphet.thinningRate`, `OAI.MatroidProphet.weightBase`, `OAI.MatroidProphet.MainAlgorithm.analyzedComparisonMass`, `OAI.MatroidProphet.MainAlgorithm.candidateLabels`, `OAI.MatroidProphet.MainAlgorithm.mainMean` and `OAI.MatroidProphet.MainAlgorithm.mainWorstRounded` (definitions bundle `OAIW2MS000` of this split).
--
--   **Used by.** The proofs of `OAI.MatroidProphet.Assigned.hidden_vector`, `OAI.MatroidProphet.Assigned.one_sample` and `OAI.MatroidProphet.Assigned.secretary` of this split import it.
-- source:
--   OpenAI, One-sample matroid prophet inequalities against an almighty adversary, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 111; paper: https://github.com/openai/math; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/MatroidProphet/Algorithm/WeightedPayoff.lean (declaration OAI.MatroidProphet.MainAlgorithm.conditional_main_payoff)

import Mathlib
import Definitions.Def_OAIW2MS000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}

theorem conditional_main_payoff (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) :
    thinningRate / (2 * densityThreshold) *
      (retainedFraction * analyzedComparisonMass M w d.H - ((2:ℝ)^21)⁻¹ *
        ∑ e ∈ candidateLabels M w d.H, levelWeight weightBase (w e)) ≤
      mainMean d (fun d' => mainWorstRounded M hE d' w) := by
  sorry

end MatroidProphet.MainAlgorithm

end OAI
end

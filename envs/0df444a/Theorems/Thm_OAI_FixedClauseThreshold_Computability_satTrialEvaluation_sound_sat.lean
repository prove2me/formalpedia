-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_Computability_satTrialEvaluation_sound_sat
-- name    : OAI.FixedClauseThreshold.Computability.satTrialEvaluation_sound_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:27:28.61515+00:00
-- url     : https://prove2.me/theorems/661e967b-238c-4329-b301-910da90a9d94
-- title:
--   OAI.FixedClauseThreshold.Computability.satTrialEvaluation_sound_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.Computability.satTrialEvaluation_sound` of [lean/OAI/Probability/SATComputability/TrialCompleteness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/TrialCompleteness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold.Computability`, with `open DilutedSpinGlass Nat.Partrec`, `open scoped NNReal`):
--
--   ```lean
--   theorem satTrialEvaluation_sound_sat {j : ℕ} (hj : satTrialEvaluation.valid j = true)
--       (hneg : satTrialEvaluation.value j < 0) :
--       limitingCenter 3 ≤ (satTrialEvaluation.density j : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.limitingCenter`, `OAI.FixedClauseThreshold.Computability.satTrialEvaluation` and `OAI.FixedClauseThreshold.Computability.TrialEvaluation` (definitions bundle `OAIQ067A002` of this split).
--
--   **Used by.** The proof of `OAI.FixedClauseThreshold.Computability.threshold_program_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/TrialCompleteness.lean (declaration OAI.FixedClauseThreshold.Computability.satTrialEvaluation_sound)

import Mathlib
import Definitions.Def_OAIQ067A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec
open scoped NNReal

theorem satTrialEvaluation_sound_sat {j : ℕ} (hj : satTrialEvaluation.valid j = true)
    (hneg : satTrialEvaluation.value j < 0) :
    limitingCenter 3 ≤ (satTrialEvaluation.density j : ℝ) := by
  sorry

end FixedClauseThreshold.Computability

end OAI
end

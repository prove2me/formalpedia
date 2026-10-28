-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_Computability_relaxedPoissonMinimum_subcritical_sat
-- name    : OAI.FixedClauseThreshold.Computability.relaxedPoissonMinimum_subcritical_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:28:56.336408+00:00
-- url     : https://prove2.me/theorems/2bc930f1-da40-4684-ba36-c8eb5bc36306
-- title:
--   OAI.FixedClauseThreshold.Computability.relaxedPoissonMinimum_subcritical_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.Computability.relaxedPoissonMinimum_subcritical` of [lean/OAI/Probability/SATComputability/SubcriticalEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/SubcriticalEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold.Computability`, with `open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology`):
--
--   ```lean
--   theorem relaxedPoissonMinimum_subcritical_sat {a : ℝ≥0}
--       (ha : (a : ℝ) < limitingCenter 3) :
--       Tendsto (fun n : ℕ => relaxedPoissonMinimum n a / n) atTop (nhds 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.limitingCenter` and `OAI.FixedClauseThreshold.Computability.relaxedPoissonMinimum` (definitions bundle `OAIQ067A002` of this split).
--
--   **Used by.** The proof of `OAI.FixedClauseThreshold.Computability.satTrialEvaluation_sound_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/SubcriticalEnergy.lean (declaration OAI.FixedClauseThreshold.Computability.relaxedPoissonMinimum_subcritical)

import Mathlib
import Definitions.Def_OAIQ067A002

section

attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

theorem relaxedPoissonMinimum_subcritical_sat {a : ℝ≥0}
    (ha : (a : ℝ) < limitingCenter 3) :
    Tendsto (fun n : ℕ => relaxedPoissonMinimum n a / n) atTop (nhds 0) := by
  sorry

end FixedClauseThreshold.Computability

end OAI
end

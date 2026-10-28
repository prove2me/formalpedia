-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_Computability_auxiliaryPoissonProbability_supercritical_sat
-- name    : OAI.FixedClauseThreshold.Computability.auxiliaryPoissonProbability_supercritical_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:24:55.139244+00:00
-- url     : https://prove2.me/theorems/18a3cf7e-27ab-430d-bb12-95a172b189f3
-- title:
--   OAI.FixedClauseThreshold.Computability.auxiliaryPoissonProbability_supercritical_sat (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.Computability.auxiliaryPoissonProbability_supercritical` of [lean/OAI/Probability/SATComputability/SupercriticalProbability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/SupercriticalProbability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold.Computability`, with `open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology`):
--
--   ```lean
--   theorem auxiliaryPoissonProbability_supercritical_sat {a : ℝ≥0}
--       (ha : limitingCenter 3 < (a : ℝ)) :
--       Tendsto (fun n => auxiliaryPoissonProbability n a) atTop (nhds 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.limitingCenter` and `OAI.FixedClauseThreshold.Computability.auxiliaryPoissonProbability` (definitions bundle `OAIQ067A002` of this split).
--
--   **Used by.** The proof of `OAI.FixedClauseThreshold.Computability.threshold_program_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/SupercriticalProbability.lean (declaration OAI.FixedClauseThreshold.Computability.auxiliaryPoissonProbability_supercritical)

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

theorem auxiliaryPoissonProbability_supercritical_sat {a : ℝ≥0}
    (ha : limitingCenter 3 < (a : ℝ)) :
    Tendsto (fun n => auxiliaryPoissonProbability n a) atTop (nhds 0) := by
  sorry

end FixedClauseThreshold.Computability

end OAI
end

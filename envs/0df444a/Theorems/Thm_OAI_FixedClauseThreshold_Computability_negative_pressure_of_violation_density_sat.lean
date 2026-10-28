-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_Computability_negative_pressure_of_violation_density_sat
-- name    : OAI.FixedClauseThreshold.Computability.negative_pressure_of_violation_density_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:26:51.452764+00:00
-- url     : https://prove2.me/theorems/91930a6d-ff44-4755-aaad-b8549299c7fa
-- title:
--   OAI.FixedClauseThreshold.Computability.negative_pressure_of_violation_density_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.Computability.negative_pressure_of_violation_density` of [lean/OAI/Probability/SATComputability/PressureUpper.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/PressureUpper.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold.Computability`, with `open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter`, `open scoped Topology NNReal`):
--
--   ```lean
--   theorem negative_pressure_of_violation_density_sat {a : ℝ≥0} (ha : 0 < a)
--       {ε : ℝ} (hε : 0 < ε)
--       (hV : ∀ᶠ n : ℕ in atTop, ε ≤ relaxedPoissonMinimum n a/n) :
--       ∃ β : ℕ, 0 < β ∧ satPressure a β < 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.Computability.satPressure` (definitions bundle `OAIQ067A001` of this split); `OAI.FixedClauseThreshold.Computability.relaxedPoissonMinimum` (definitions bundle `OAIQ067A002` of this split).
--
--   **Used by.** The proof of `OAI.FixedClauseThreshold.Computability.threshold_program_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/PressureUpper.lean (declaration OAI.FixedClauseThreshold.Computability.negative_pressure_of_violation_density)

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
open scoped Topology NNReal

theorem negative_pressure_of_violation_density_sat {a : ℝ≥0} (ha : 0 < a)
    {ε : ℝ} (hε : 0 < ε)
    (hV : ∀ᶠ n : ℕ in atTop, ε ≤ relaxedPoissonMinimum n a/n) :
    ∃ β : ℕ, 0 < β ∧ satPressure a β < 0 := by
  sorry

end FixedClauseThreshold.Computability

end OAI
end

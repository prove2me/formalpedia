-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_Computability_threshold_program_sat
-- name    : OAI.FixedClauseThreshold.Computability.threshold_program_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:29:54.717298+00:00
-- url     : https://prove2.me/theorems/b23a9504-96f6-4416-9eb7-c11abb8dac5f
-- title:
--   OAI.FixedClauseThreshold.Computability.threshold_program_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.Computability.threshold_program` of [lean/OAI/Probability/SATComputability/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold.Computability`, with `open Filter`, `open scoped Topology NNReal`):
--
--   ```lean
--   theorem threshold_program_sat :
--       ∃ (q : ℕ → ℚ) (c : Nat.Partrec.Code),
--         Computable q ∧
--         (∀ r, c.eval r = Part.some (Encodable.encode (q r))) ∧
--         (∀ r, |(q r : ℝ)-limitingCenter 3| ≤ (2^r : ℝ)⁻¹)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable` (definitions bundle `OAIQ067A000` of this split); `OAI.FixedClauseThreshold.limitingCenter` (definitions bundle `OAIQ067A002` of this split).
--
--   **Used by.** The proof of `OAI.FixedClauseThreshold.Computability.main` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/Main.lean (declaration OAI.FixedClauseThreshold.Computability.threshold_program)

import Mathlib
import Definitions.Def_OAIQ067A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology NNReal

theorem threshold_program_sat :
    ∃ (q : ℕ → ℚ) (c : Nat.Partrec.Code),
      Computable q ∧
      (∀ r, c.eval r = Part.some (Encodable.encode (q r))) ∧
      (∀ r, |(q r : ℝ)-limitingCenter 3| ≤ (2^r : ℝ)⁻¹) := by
  sorry

end FixedClauseThreshold.Computability

end OAI
end

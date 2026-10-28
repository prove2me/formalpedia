-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_Computability_exists_lowerProgram_sat
-- name    : OAI.FixedClauseThreshold.Computability.exists_lowerProgram_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:26:45.787396+00:00
-- url     : https://prove2.me/theorems/9f89e0dd-af60-44f2-913f-8607d53313a0
-- title:
--   OAI.FixedClauseThreshold.Computability.exists_lowerProgram_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.Computability.exists_lowerProgram` of [lean/OAI/Probability/SATComputability/LowerProgram.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/LowerProgram.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold.Computability`, with `open Filter RapidForcing.EffectiveArithmetic`, `open scoped Topology`):
--
--   ```lean
--   theorem exists_lowerProgram_sat :
--       ∃ lower : ℕ → ℚ, Computable lower ∧
--         (∀ i, (lower i : ℝ) ≤ limitingCenter 3) ∧
--         (∀ ε : ℝ, 0 < ε → ∃ i, limitingCenter 3 - ε < (lower i : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable` (definitions bundle `OAIQ067A000` of this split); `OAI.FixedClauseThreshold.limitingCenter` (definitions bundle `OAIQ067A002` of this split).
--
--   **Used by.** The proof of `OAI.FixedClauseThreshold.Computability.threshold_program_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/LowerProgram.lean (declaration OAI.FixedClauseThreshold.Computability.exists_lowerProgram)

import Mathlib
import Definitions.Def_OAIQ067A002

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter RapidForcing.EffectiveArithmetic
open scoped Topology

attribute [local irreducible] rationalCenter

theorem exists_lowerProgram_sat :
    ∃ lower : ℕ → ℚ, Computable lower ∧
      (∀ i, (lower i : ℝ) ≤ limitingCenter 3) ∧
      (∀ ε : ℝ, 0 < ε → ∃ i, limitingCenter 3 - ε < (lower i : ℝ)) := by
  sorry

end FixedClauseThreshold.Computability

end OAI
end

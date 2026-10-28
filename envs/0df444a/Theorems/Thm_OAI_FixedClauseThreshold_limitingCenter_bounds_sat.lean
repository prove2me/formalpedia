-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_limitingCenter_bounds_sat
-- name    : OAI.FixedClauseThreshold.limitingCenter_bounds_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:31:01.396775+00:00
-- url     : https://prove2.me/theorems/2dbf27f4-5a3f-4282-b847-42ca98c4a6f5
-- title:
--   OAI.FixedClauseThreshold.limitingCenter_bounds_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.limitingCenter_bounds` of [lean/OAI/Probability/RandomSAT/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RandomSAT/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold`, with `open Finset`):
--
--   ```lean
--   theorem limitingCenter_bounds_sat (k : ℕ) (hk : 3 ≤ k) :
--       lowerCenterBound ≤ limitingCenter k ∧ limitingCenter k ≤ (2 : ℝ)^k + 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.lowerCenterBound` (definitions bundle `OAIQ067A000` of this split); `OAI.FixedClauseThreshold.limitingCenter` (definitions bundle `OAIQ067A002` of this split).
--
--   **Used by.** The proofs of `OAI.FixedClauseThreshold.Computability.threshold_program_sat`, `OAI.FixedClauseThreshold.limitingCenter_lt_cap_sat` and `OAI.FixedClauseThreshold.limitingCenter_pos_sat` of this split import it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RandomSAT/Main.lean (declaration OAI.FixedClauseThreshold.limitingCenter_bounds)

import Mathlib
import Definitions.Def_OAIQ067A002

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem limitingCenter_bounds_sat (k : ℕ) (hk : 3 ≤ k) :
    lowerCenterBound ≤ limitingCenter k ∧ limitingCenter k ≤ (2 : ℝ)^k + 1 := by
  sorry

end

end FixedClauseThreshold

end OAI
end

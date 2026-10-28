-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_center_lower_of_auxiliary_probability_sat
-- name    : OAI.FixedClauseThreshold.center_lower_of_auxiliary_probability_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:27:52.054566+00:00
-- url     : https://prove2.me/theorems/537bd08f-a5a9-487b-8ff0-9f2fdc519ead
-- title:
--   OAI.FixedClauseThreshold.center_lower_of_auxiliary_probability_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.center_lower_of_auxiliary_probability` of [lean/OAI/Probability/RandomSAT/CenterComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RandomSAT/CenterComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold`, with `open Finset`):
--
--   ```lean
--   theorem center_lower_of_auxiliary_probability_sat {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
--       {c : ℝ} (hc0 : 0 ≤ c) (hcL : c ≤ capMultiplier k)
--       (hprob : concentrationError n k < auxiliaryProbability n k ⌊c * n⌋₊) :
--       c - 2 * densityWindow n k < center n k
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.capMultiplier`, `OAI.FixedClauseThreshold.center`, `OAI.FixedClauseThreshold.concentrationError` and `OAI.FixedClauseThreshold.densityWindow` (definitions bundle `OAIQ067A000` of this split); `OAI.FixedClauseThreshold.auxiliaryProbability` (definitions bundle `OAIQ067A002` of this split).
--
--   **Used by.** The proofs of `OAI.FixedClauseThreshold.Computability.auxiliaryPoissonProbability_supercritical_sat`, `OAI.FixedClauseThreshold.Computability.exists_lowerProgram_sat`, `OAI.FixedClauseThreshold.Computability.main`, `OAI.FixedClauseThreshold.limitingCenter_bounds_sat` and `OAI.FixedClauseThreshold.subcritical_limit_sat` of this split import it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RandomSAT/CenterComparison.lean (declaration OAI.FixedClauseThreshold.center_lower_of_auxiliary_probability)

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

theorem center_lower_of_auxiliary_probability_sat {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    {c : ℝ} (hc0 : 0 ≤ c) (hcL : c ≤ capMultiplier k)
    (hprob : concentrationError n k < auxiliaryProbability n k ⌊c * n⌋₊) :
    c - 2 * densityWindow n k < center n k := by
  sorry

end

end FixedClauseThreshold

end OAI
end

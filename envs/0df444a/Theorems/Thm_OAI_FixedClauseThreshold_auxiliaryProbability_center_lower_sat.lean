-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_auxiliaryProbability_center_lower_sat
-- name    : OAI.FixedClauseThreshold.auxiliaryProbability_center_lower_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:29:23.4206+00:00
-- url     : https://prove2.me/theorems/7865d36c-9751-4200-aad9-b3cc106c15e3
-- title:
--   OAI.FixedClauseThreshold.auxiliaryProbability_center_lower_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.auxiliaryProbability_center_lower` of [lean/OAI/Probability/RandomSAT/Transfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RandomSAT/Transfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold`, with `open Finset`):
--
--   ```lean
--   theorem auxiliaryProbability_center_lower_sat {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
--       (hnrep : 2 * repeatPairs k ≤ n) (herror : concentrationError n k ≤ 1 / 2)
--       (hgap : (m : ℝ) + fluctuationWindow n k ≤ (n : ℝ) * center n k) :
--       transferLower k ≤ auxiliaryProbability n k m
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.center`, `OAI.FixedClauseThreshold.concentrationError`, `OAI.FixedClauseThreshold.fluctuationWindow`, `OAI.FixedClauseThreshold.repeatPairs` and `OAI.FixedClauseThreshold.transferLower` (definitions bundle `OAIQ067A000` of this split); `OAI.FixedClauseThreshold.auxiliaryProbability` (definitions bundle `OAIQ067A002` of this split).
--
--   **Used by.** The proofs of `OAI.FixedClauseThreshold.Computability.auxiliaryPoissonProbability_supercritical_sat`, `OAI.FixedClauseThreshold.Computability.exists_lowerProgram_sat`, `OAI.FixedClauseThreshold.Computability.main`, `OAI.FixedClauseThreshold.limitingCenter_bounds_sat` and `OAI.FixedClauseThreshold.subcritical_limit_sat` of this split import it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RandomSAT/Transfer.lean (declaration OAI.FixedClauseThreshold.auxiliaryProbability_center_lower)

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

theorem auxiliaryProbability_center_lower_sat {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (hnrep : 2 * repeatPairs k ≤ n) (herror : concentrationError n k ≤ 1 / 2)
    (hgap : (m : ℝ) + fluctuationWindow n k ≤ (n : ℝ) * center n k) :
    transferLower k ≤ auxiliaryProbability n k m := by
  sorry

end

end FixedClauseThreshold

end OAI
end

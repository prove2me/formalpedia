-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_properSATProbability_center_upper_sat
-- name    : OAI.FixedClauseThreshold.properSATProbability_center_upper_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:23:50.604041+00:00
-- url     : https://prove2.me/theorems/03ca1ff6-558f-4690-bb1c-8fbca5570711
-- title:
--   OAI.FixedClauseThreshold.properSATProbability_center_upper_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.properSATProbability_center_upper` of [lean/OAI/Probability/RandomSAT/Concentration.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RandomSAT/Concentration.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold`, with `open Finset`):
--
--   ```lean
--   theorem properSATProbability_center_upper_sat {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
--       (hm : m ≤ mainCap n k)
--       (hgap : (n : ℝ) * center n k + fluctuationWindow n k ≤ m) :
--       properSATProbability n k m ≤ concentrationError n k
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.center`, `OAI.FixedClauseThreshold.concentrationError`, `OAI.FixedClauseThreshold.fluctuationWindow` and `OAI.FixedClauseThreshold.mainCap` (definitions bundle `OAIQ067A000` of this split); `OAI.FixedClauseThreshold.properSATProbability` (the published bundle `Def_SATComputability`).
--
--   **Used by.** The proofs of `OAI.FixedClauseThreshold.Computability.auxiliaryPoissonProbability_supercritical_sat`, `OAI.FixedClauseThreshold.Computability.main` and `OAI.FixedClauseThreshold.center_lower_of_auxiliary_probability_sat` of this split import it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RandomSAT/Concentration.lean (declaration OAI.FixedClauseThreshold.properSATProbability_center_upper)

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_OAIQ067A000

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

theorem properSATProbability_center_upper_sat {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (hm : m ≤ mainCap n k)
    (hgap : (n : ℝ) * center n k + fluctuationWindow n k ≤ m) :
    properSATProbability n k m ≤ concentrationError n k := by
  sorry

end

end FixedClauseThreshold

end OAI
end

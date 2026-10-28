-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_subcritical_limit_sat
-- name    : OAI.FixedClauseThreshold.subcritical_limit_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:30:32.637713+00:00
-- url     : https://prove2.me/theorems/039e0ab9-c1f2-4bfa-a1bd-15c0b8813d39
-- title:
--   OAI.FixedClauseThreshold.subcritical_limit_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.subcritical_limit` of [lean/OAI/Probability/RandomSAT/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RandomSAT/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold`, with `open Finset`):
--
--   ```lean
--   theorem subcritical_limit_sat (k : ℕ) (hk : 3 ≤ k) (c : ℝ) (hc0 : 0 ≤ c)
--       (hc : c < limitingCenter k) :
--       Filter.Tendsto (fun n : ℕ => properSATProbability n k ⌊c * (n : ℝ)⌋₊)
--         Filter.atTop (nhds 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.limitingCenter` (definitions bundle `OAIQ067A002` of this split); `OAI.FixedClauseThreshold.properSATProbability` (the published bundle `Def_SATComputability`).
--
--   **Used by.** The proofs of `OAI.FixedClauseThreshold.Computability.main` and `OAI.FixedClauseThreshold.Computability.relaxedPoissonMinimum_subcritical_sat` of this split import it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RandomSAT/Main.lean (declaration OAI.FixedClauseThreshold.subcritical_limit)

import Mathlib
import Definitions.Def_SATComputability
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

theorem subcritical_limit_sat (k : ℕ) (hk : 3 ≤ k) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c < limitingCenter k) :
    Filter.Tendsto (fun n : ℕ => properSATProbability n k ⌊c * (n : ℝ)⌋₊)
      Filter.atTop (nhds 1) := by
  sorry

end

end FixedClauseThreshold

end OAI
end

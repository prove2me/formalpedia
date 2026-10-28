-- Prove2me | Theorems.Thm_OAI_Thorp_mixingTime_isTheta_log_q3
-- name    : OAI.Thorp.mixingTime_isTheta_log_q3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T03:02:28.396851+00:00
-- url     : https://prove2.me/theorems/ad55bf55-d45a-47e4-b4ce-12955f626edf
-- title:
--   OAI.Thorp.mixingTime_isTheta_log_q3: intermediate lemma from OpenAI, Optimal-order mixing of the Thorp shuffle
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThorpResults.remaining_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Optimal-order mixing of the Thorp shuffle*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Thorp.mixingTime_isTheta_log` of [lean/OAI/Probability/ThorpResults/ThorpShuffle/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpResults/ThorpShuffle/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Thorp`, with `open scoped BigOperators ComplexConjugate InnerProductSpace`, `open Filter Topology`):
--
--   ```lean
--   theorem mixingTime_isTheta_log_q3 :
--       Asymptotics.IsTheta atTop (fun d : ℕ => (mixingTime d : ℝ))
--         (fun d : ℕ => Real.log (2^d : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Thorp.mixingTime` (the published bundle `Def_ThorpRemaining`).
--
--   **Used by.** The proof of `OAI.ThorpResults.remaining_main` of this split imports it.
-- source:
--   OpenAI, Optimal-order mixing of the Thorp shuffle, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Optimal-order-mixing-of-the-Thorp-shuffle-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpResults/ThorpShuffle/Main.lean (declaration OAI.Thorp.mixingTime_isTheta_log)

import Mathlib
import Definitions.Def_ThorpRemaining

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp

theorem mixingTime_isTheta_log_q3 :
    Asymptotics.IsTheta atTop (fun d : ℕ => (mixingTime d : ℝ))
      (fun d : ℕ => Real.log (2^d : ℝ)) := by
  sorry

end Thorp

end

end OAI
end

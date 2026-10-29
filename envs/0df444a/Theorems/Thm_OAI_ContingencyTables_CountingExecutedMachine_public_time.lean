-- Prove2me | Theorems.Thm_OAI_ContingencyTables_CountingExecutedMachine_public_time
-- name    : OAI.ContingencyTables.CountingExecutedMachine.public_time
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T03:27:08.123522+00:00
-- url     : https://prove2.me/theorems/4598976c-d940-4ddb-9400-89b577aaa439
-- title:
--   OAI.ContingencyTables.CountingExecutedMachine.public_time: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.CountingExecutedMachine.public_time` of [lean/OAI/Combinatorics/ContingencyTables/Counting/CountingExecutedMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CountingExecutedMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.CountingExecutedMachine`, with `open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream`, `open scoped Classical`):
--
--   ```lean
--   theorem public_time (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1) :
--       ∃ C d : ℕ,0<C ∧ ∀ (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
--         (epsilon delta : ℚ),0<epsilon→0<delta→
--         machineTime (Algorithms.encodeCountingInput r c b epsilon delta) ≤
--           Algorithms.countingTime C d r c b epsilon delta
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContingencyTables.PublishedEdmondsKarp.EdmondsKarp1972Theorem1` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.CountingExecutedMachine.machineTime` (definitions bundle `OAIQ089A009` of this split); `OAI.ContingencyTables.Algorithms.countingTime` and `OAI.ContingencyTables.Algorithms.encodeCountingInput` (the published bundle `Def_ContingencyTables`).
--
--   **Used by.** The proof of `OAI.ContingencyTables.counting` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CountingExecutedMachine.lean (declaration OAI.ContingencyTables.CountingExecutedMachine.public_time)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.CountingExecutedMachine
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open scoped Classical
noncomputable section

theorem public_time (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1) :
    ∃ C d : ℕ,0<C ∧ ∀ (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
      (epsilon delta : ℚ),0<epsilon→0<delta→
      machineTime (Algorithms.encodeCountingInput r c b epsilon delta) ≤
        Algorithms.countingTime C d r c b epsilon delta := by
  sorry

end
end ContingencyTables.CountingExecutedMachine

end OAI
end

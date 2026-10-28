-- Prove2me | Theorems.Thm_OAI_RyserCoveringCounterexample_Construction_exists_prime_goodGadget
-- name    : OAI.RyserCoveringCounterexample.Construction.exists_prime_goodGadget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T04:27:10.86748+00:00
-- url     : https://prove2.me/theorems/05951300-dd89-4de9-a2f6-95e92fde8144
-- title:
--   OAI.RyserCoveringCounterexample.Construction.exists_prime_goodGadget: intermediate lemma from OpenAI, A counterexample to Ryser's covering conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Ryser's covering conjecture*, OpenAI Math Release, September 23, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RyserCoveringCounterexample.Construction.exists_prime_goodGadget` of [lean/OAI/Combinatorics/Ryser/Construction/GadgetExistence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Ryser/Construction/GadgetExistence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RyserCoveringCounterexample.Construction`, with `open Filter Topology`):
--
--   ```lean
--   theorem exists_prime_goodGadget :
--       ∃ (p : ℕ) (hp : p.Prime), 5 < p ∧ p % 3 = 2 ∧
--         letI : Fact p.Prime := ⟨hp⟩
--         ∃ a : GadgetOutcome (ZMod p), GoodGadget a
--   ```
--
--   **Definitions.** The statement is written with `OAI.RyserCoveringCounterexample.Construction.GadgetOutcome` and `OAI.RyserCoveringCounterexample.Construction.GoodGadget` (definitions bundle `OAIW2RY000` of this split).
--
--   **Used by.** The proof of `OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank` of this split imports it.
-- source:
--   OpenAI, A counterexample to Ryser's covering conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Ryser/Construction/GadgetExistence.lean (declaration OAI.RyserCoveringCounterexample.Construction.exists_prime_goodGadget)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIW2RY000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
noncomputable section

namespace RyserCoveringCounterexample.Construction

theorem exists_prime_goodGadget :
    ∃ (p : ℕ) (hp : p.Prime), 5 < p ∧ p % 3 = 2 ∧
      letI : Fact p.Prime := ⟨hp⟩
      ∃ a : GadgetOutcome (ZMod p), GoodGadget a := by
  sorry

end RyserCoveringCounterexample.Construction

end

end OAI
end

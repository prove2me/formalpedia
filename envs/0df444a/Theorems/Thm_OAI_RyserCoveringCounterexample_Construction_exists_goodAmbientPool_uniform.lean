-- Prove2me | Theorems.Thm_OAI_RyserCoveringCounterexample_Construction_exists_goodAmbientPool_uniform
-- name    : OAI.RyserCoveringCounterexample.Construction.exists_goodAmbientPool_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T04:27:21.961126+00:00
-- url     : https://prove2.me/theorems/4f9a5f96-a6e1-4ad5-a208-8286d748d23f
-- title:
--   OAI.RyserCoveringCounterexample.Construction.exists_goodAmbientPool_uniform: intermediate lemma from OpenAI, A counterexample to Ryser's covering conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Ryser's covering conjecture*, OpenAI Math Release, September 23, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RyserCoveringCounterexample.Construction.exists_goodAmbientPool_uniform` of [lean/OAI/Combinatorics/Ryser/Construction/AmbientPoolExistence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Ryser/Construction/AmbientPoolExistence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RyserCoveringCounterexample.Construction`, with `open scoped Classical`):
--
--   ```lean
--   theorem exists_goodAmbientPool_uniform
--       (u v : k) (huv : u ≠ v) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
--       (hs : 2 ≤ Fintype.card k) :
--       ∃ K Q : ℕ, 6 ≤ K ∧
--         ∀ (F : Type uf) [Field F] [Fintype F] [DecidableEq F] (σ : k →+* F),
--           Q ≤ Fintype.card F → Incidence.SmallProperSubfields F →
--           (1 + ambientDeletionDelta (Fintype.card k) K / 10 * Fintype.card F <
--             ambientDeletionDelta (Fintype.card k) K * Fintype.card F / 2) ∧
--           ∃ pool : AmbientPool σ K, GoodAmbientPool σ u v huv a ha K pool
--   ```
--
--   **Definitions.** The statement is written with `OAI.RyserCoveringCounterexample.Construction.AmbientPool`, `OAI.RyserCoveringCounterexample.Construction.GadgetOutcome`, `OAI.RyserCoveringCounterexample.Construction.GoodAmbientPool`, `OAI.RyserCoveringCounterexample.Construction.OriginalLineDensity`, `OAI.RyserCoveringCounterexample.Construction.ambientDeletionDelta` and `OAI.RyserCoveringCounterexample.Incidence.SmallProperSubfields` (definitions bundle `OAIW2RY000` of this split).
--
--   **Used by.** The proof of `OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank` of this split imports it.
-- source:
--   OpenAI, A counterexample to Ryser's covering conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Ryser/Construction/AmbientPoolExistence.lean (declaration OAI.RyserCoveringCounterexample.Construction.exists_goodAmbientPool_uniform)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIW2RY000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace RyserCoveringCounterexample.Construction

universe uk uf

variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]

theorem exists_goodAmbientPool_uniform
    (u v : k) (huv : u ≠ v) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (hs : 2 ≤ Fintype.card k) :
    ∃ K Q : ℕ, 6 ≤ K ∧
      ∀ (F : Type uf) [Field F] [Fintype F] [DecidableEq F] (σ : k →+* F),
        Q ≤ Fintype.card F → Incidence.SmallProperSubfields F →
        (1 + ambientDeletionDelta (Fintype.card k) K / 10 * Fintype.card F <
          ambientDeletionDelta (Fintype.card k) K * Fintype.card F / 2) ∧
        ∃ pool : AmbientPool σ K, GoodAmbientPool σ u v huv a ha K pool := by
  sorry

end RyserCoveringCounterexample.Construction

end

end OAI
end

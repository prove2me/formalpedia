-- Prove2me | Theorems.Thm_OAI_RyserCoveringCounterexample_Selection_compatible_selection_uniform
-- name    : OAI.RyserCoveringCounterexample.Selection.compatible_selection_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T04:28:48.993527+00:00
-- url     : https://prove2.me/theorems/48bf3c41-e5d0-4a48-a509-1de925d43d24
-- title:
--   OAI.RyserCoveringCounterexample.Selection.compatible_selection_uniform: intermediate lemma from OpenAI, A counterexample to Ryser's covering conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Ryser's covering conjecture*, OpenAI Math Release, September 23, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RyserCoveringCounterexample.Selection.compatible_selection_uniform` of [lean/OAI/Combinatorics/Ryser/Selection/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Ryser/Selection/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RyserCoveringCounterexample.Selection`):
--
--   ```lean
--   theorem compatible_selection_uniform (D : ℕ) (hD : 1 ≤ D) :
--       ∃ K : ℕ, 6 ≤ K ∧
--         ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ,
--           ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
--             (n : ℕ) (data : Data F n),
--             Bounded D data → Q ≤ Fintype.card F →
--               1 - ε ≤ (poolLaw F n K).prob
--                 (fun pool => HasCompatibleChoice data pool)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RyserCoveringCounterexample.Point`, `OAI.RyserCoveringCounterexample.FiniteLaw.prob`, `OAI.RyserCoveringCounterexample.Selection.Data`, `OAI.RyserCoveringCounterexample.Selection.HasCompatibleChoice`, `OAI.RyserCoveringCounterexample.Selection.Pool` and `OAI.RyserCoveringCounterexample.Selection.Position` (definitions bundle `OAIW2RY000` of this split); `OAI.RyserCoveringCounterexample.Selection.Bounded` and `OAI.RyserCoveringCounterexample.Selection.poolLaw` (definitions bundle `OAIW2RY002` of this split).
--
--   **Used by.** The proof of `OAI.RyserCoveringCounterexample.Construction.exists_goodAmbientPool_uniform` of this split imports it.
-- source:
--   OpenAI, A counterexample to Ryser's covering conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Ryser/Selection/Main.lean (declaration OAI.RyserCoveringCounterexample.Selection.compatible_selection_uniform)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIW2RY002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace RyserCoveringCounterexample.Selection

theorem compatible_selection_uniform (D : ℕ) (hD : 1 ≤ D) :
    ∃ K : ℕ, 6 ≤ K ∧
      ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ,
        ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
          (n : ℕ) (data : Data F n),
          Bounded D data → Q ≤ Fintype.card F →
            1 - ε ≤ (poolLaw F n K).prob
              (fun pool => HasCompatibleChoice data pool) := by
  sorry

end RyserCoveringCounterexample.Selection

end OAI
end

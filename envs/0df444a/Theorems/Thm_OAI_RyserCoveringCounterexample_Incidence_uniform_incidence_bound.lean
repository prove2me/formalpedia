-- Prove2me | Theorems.Thm_OAI_RyserCoveringCounterexample_Incidence_uniform_incidence_bound
-- name    : OAI.RyserCoveringCounterexample.Incidence.uniform_incidence_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T04:27:01.131952+00:00
-- url     : https://prove2.me/theorems/76242085-f17a-4605-b513-114a4c76f3bb
-- title:
--   OAI.RyserCoveringCounterexample.Incidence.uniform_incidence_bound: intermediate lemma from OpenAI, A counterexample to Ryser's covering conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Ryser's covering conjecture*, OpenAI Math Release, September 23, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RyserCoveringCounterexample.Incidence.uniform_incidence_bound` of [lean/OAI/Combinatorics/Ryser/Incidence/Uniform.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Ryser/Incidence/Uniform.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RyserCoveringCounterexample.Incidence`):
--
--   ```lean
--   theorem uniform_incidence_bound (F : Type*) [Field F] [Fintype F] [DecidableEq F]
--       (hq : incidenceThreshold ≤ Fintype.card F) (hsub : SmallProperSubfields F)
--       (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
--       (hP : (P.card : ℝ) ≤ (Fintype.card F : ℝ) ^ (1 + savingExponent))
--       (hL : (L.card : ℝ) ≤ (Fintype.card F : ℝ) ^ (1 + savingExponent)) :
--       (incidenceCount ProjectiveIncidence P L : ℝ) ≤
--         (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 - savingExponent)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RyserCoveringCounterexample.ProjectiveIncidence`, `OAI.RyserCoveringCounterexample.ProjectiveLine`, `OAI.RyserCoveringCounterexample.ProjectivePoint`, `OAI.RyserCoveringCounterexample.Incidence.SmallProperSubfields`, `OAI.RyserCoveringCounterexample.Incidence.incidenceCount`, `OAI.RyserCoveringCounterexample.Incidence.incidenceThreshold` and `OAI.RyserCoveringCounterexample.Incidence.savingExponent` (definitions bundle `OAIW2RY000` of this split).
--
--   **Used by.** The proof of `OAI.RyserCoveringCounterexample.LineCover.goodLineCover_of_goodCounts_goodTuples` of this split imports it.
-- source:
--   OpenAI, A counterexample to Ryser's covering conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Ryser/Incidence/Uniform.lean (declaration OAI.RyserCoveringCounterexample.Incidence.uniform_incidence_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIW2RY000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section

theorem uniform_incidence_bound (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hq : incidenceThreshold ≤ Fintype.card F) (hsub : SmallProperSubfields F)
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    (hP : (P.card : ℝ) ≤ (Fintype.card F : ℝ) ^ (1 + savingExponent))
    (hL : (L.card : ℝ) ≤ (Fintype.card F : ℝ) ^ (1 + savingExponent)) :
    (incidenceCount ProjectiveIncidence P L : ℝ) ≤
      (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 - savingExponent) := by
  sorry

end
end RyserCoveringCounterexample.Incidence

end OAI
end

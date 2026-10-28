-- Prove2me | Theorems.Thm_OAI_Balanced_ProfileCountingAssembly_profileCounting_of_sourceRareTailBound
-- name    : OAI.Balanced.ProfileCountingAssembly.profileCounting_of_sourceRareTailBound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:12:13.144466+00:00
-- url     : https://prove2.me/theorems/98905eec-4b60-4459-af65-b8869be7f1f8
-- title:
--   OAI.Balanced.ProfileCountingAssembly.profileCounting_of_sourceRareTailBound: intermediate lemma from OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Balanced.main_result`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)*, OpenAI Math Release, September 27, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Balanced.ProfileCountingAssembly.profileCounting_of_sourceRareTailBound` of [lean/OAI/Combinatorics/BalancedRyser/Profiles/ProfileCountingAssembly.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Profiles/ProfileCountingAssembly.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Balanced.ProfileCountingAssembly`, with `open scoped BigOperators`, `open ProfileScheduledMargin ProfileWitnessPayment`):
--
--   ```lean
--   theorem profileCounting_of_sourceRareTailBound
--       (hrare : ∀ k : ℕ, 1 ≤ k → SourceRareTailBound.{u} k) :
--       ProfileCountingResult.{u}
--   ```
--
--   **Definitions.** The statement is written with `OAI.Balanced.ProfileCountingResult` and `OAI.Balanced.ProfileCountingAssembly.SourceRareTailBound` (definitions bundle `OAIQ63Br002` of this split).
--
--   **Used by.** The proof of `OAI.Balanced.robust_deletion` of this split imports it.
-- source:
--   OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Profiles/ProfileCountingAssembly.lean (declaration OAI.Balanced.ProfileCountingAssembly.profileCounting_of_sourceRareTailBound)

import Mathlib
import Definitions.Def_OAIQ63Br002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.ProfileCountingAssembly

universe u

open ProfileScheduledMargin ProfileWitnessPayment

theorem profileCounting_of_sourceRareTailBound
    (hrare : ∀ k : ℕ, 1 ≤ k → SourceRareTailBound.{u} k) :
    ProfileCountingResult.{u} := by
  sorry

end Balanced.ProfileCountingAssembly

end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_Balanced_CandidateIncidenceTests_tendsto_smallGood
-- name    : OAI.Balanced.CandidateIncidenceTests.tendsto_smallGood
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:08:50.498102+00:00
-- url     : https://prove2.me/theorems/f353d1e0-5ac4-4b73-b351-4a9c93d4e48a
-- title:
--   OAI.Balanced.CandidateIncidenceTests.tendsto_smallGood: intermediate lemma from OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Balanced.main_result`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)*, OpenAI Math Release, September 27, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Balanced.CandidateIncidenceTests.tendsto_smallGood` of [lean/OAI/Combinatorics/BalancedRyser/Incidence/CandidateSmallIncidence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Incidence/CandidateSmallIncidence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Balanced.CandidateIncidenceTests`, with `open MeasureTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem tendsto_smallGood
--       (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
--       [∀ n, DecidableEq (F n)]
--       (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
--       Tendsto (fun n => offsetEventProbability (F := F n)
--         {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
--         atTop (𝓝 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Balanced.MergedPairs`, `OAI.Balanced.offsetEventProbability` and `OAI.Balanced.CandidateIncidenceTests.SmallGood` (definitions bundle `OAIQ63Br000` of this split).
--
--   **Used by.** The proof of `OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_size_estimate` of this split imports it.
-- source:
--   OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Incidence/CandidateSmallIncidence.lean (declaration OAI.Balanced.CandidateIncidenceTests.tendsto_smallGood)

import Mathlib
import Definitions.Def_OAIQ63Br000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Balanced.CandidateIncidenceTests

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem tendsto_smallGood
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
      atTop (𝓝 1) := by
  sorry

end Balanced.CandidateIncidenceTests

end

end OAI
end

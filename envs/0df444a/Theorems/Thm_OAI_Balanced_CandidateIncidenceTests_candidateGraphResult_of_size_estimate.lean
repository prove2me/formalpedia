-- Prove2me | Theorems.Thm_OAI_Balanced_CandidateIncidenceTests_candidateGraphResult_of_size_estimate
-- name    : OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_size_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:08:16.321537+00:00
-- url     : https://prove2.me/theorems/3df54340-c06b-42bb-8cdb-1f8195f8ec5a
-- title:
--   OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_size_estimate: intermediate lemma from OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Balanced.main_result`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)*, OpenAI Math Release, September 27, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_size_estimate` of [lean/OAI/Combinatorics/BalancedRyser/Incidence/CandidateIncidenceCompletion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Incidence/CandidateIncidenceCompletion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Balanced.CandidateIncidenceTests`, with `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem candidateGraphResult_of_size_estimate (c : ℝ) (hc : 0 < c)
--       (hsize : ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
--         [∀ n, DecidableEq (F n)],
--         Tendsto (fun n => Fintype.card (F n)) atTop atTop →
--         Tendsto (fun n => offsetEventProbability (F := F n) {M | SizeGood M c})
--           atTop (𝓝 1)) : CandidateGraphResult.{u}
--   ```
--
--   **Definitions.** The statement is written with `OAI.Balanced.CandidateGraphResult`, `OAI.Balanced.MergedPairs`, `OAI.Balanced.offsetEventProbability` and `OAI.Balanced.CandidateIncidenceTests.SizeGood` (definitions bundle `OAIQ63Br000` of this split).
--
--   **Used by.** The proof of `OAI.Balanced.candidateGraph_proof` of this split imports it.
-- source:
--   OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Incidence/CandidateIncidenceCompletion.lean (declaration OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_size_estimate)

import Mathlib
import Definitions.Def_OAIQ63Br000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Balanced.CandidateIncidenceTests

universe u

theorem candidateGraphResult_of_size_estimate (c : ℝ) (hc : 0 < c)
    (hsize : ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
      [∀ n, DecidableEq (F n)],
      Tendsto (fun n => Fintype.card (F n)) atTop atTop →
      Tendsto (fun n => offsetEventProbability (F := F n) {M | SizeGood M c})
        atTop (𝓝 1)) : CandidateGraphResult.{u} := by
  sorry

end Balanced.CandidateIncidenceTests

end

end OAI
end

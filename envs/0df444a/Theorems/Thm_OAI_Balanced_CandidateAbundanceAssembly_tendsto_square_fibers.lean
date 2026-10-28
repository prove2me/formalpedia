-- Prove2me | Theorems.Thm_OAI_Balanced_CandidateAbundanceAssembly_tendsto_square_fibers
-- name    : OAI.Balanced.CandidateAbundanceAssembly.tendsto_square_fibers
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:09:53.310548+00:00
-- url     : https://prove2.me/theorems/b7cf4110-1cdb-421f-86cd-dad6b635c032
-- title:
--   OAI.Balanced.CandidateAbundanceAssembly.tendsto_square_fibers: intermediate lemma from OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Balanced.main_result`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)*, OpenAI Math Release, September 27, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Balanced.CandidateAbundanceAssembly.tendsto_square_fibers` of [lean/OAI/Combinatorics/BalancedRyser/Candidates/CandidateAbundanceAssembly.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Candidates/CandidateAbundanceAssembly.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Balanced.CandidateAbundanceAssembly`, with `open scoped Classical Topology`, `open Filter MeasureTheory TupleAlignment CandidateValidityAssembly CandidatePairs`):
--
--   ```lean
--   theorem tendsto_square_fibers
--       (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
--       Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
--         ∀ g, (rootFiberSquareCount M g : ℝ) ≤
--           pairLinearThreshold * Fintype.card (F n)}) atTop (𝓝 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Balanced.Direction`, `OAI.Balanced.MergedPairs`, `OAI.Balanced.offsetEventProbability` and `OAI.Balanced.CandidatePairs.pairLinearThreshold` (definitions bundle `OAIQ63Br000` of this split); `OAI.Balanced.TupleAlignment.rootFiberSquareCount` (definitions bundle `OAIQ63Br003` of this split).
--
--   **Used by.** The proof of `OAI.Balanced.ExternalWitnessTail.candidateSlots_of_uniform_moment` of this split imports it.
-- source:
--   OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Candidates/CandidateAbundanceAssembly.lean (declaration OAI.Balanced.CandidateAbundanceAssembly.tendsto_square_fibers)

import Mathlib
import Definitions.Def_OAIQ63Br003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateAbundanceAssembly

noncomputable section
open scoped Classical Topology
open Filter MeasureTheory TupleAlignment CandidateValidityAssembly CandidatePairs

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

section Limits
variable (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
  [∀ n, DecidableEq (F n)]

theorem tendsto_square_fibers
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∀ g, (rootFiberSquareCount M g : ℝ) ≤
        pairLinearThreshold * Fintype.card (F n)}) atTop (𝓝 1) := by
  sorry

end Limits
end
end Balanced.CandidateAbundanceAssembly

end OAI
end

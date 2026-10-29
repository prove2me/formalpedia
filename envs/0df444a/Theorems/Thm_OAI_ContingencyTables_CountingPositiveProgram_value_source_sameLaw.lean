-- Prove2me | Theorems.Thm_OAI_ContingencyTables_CountingPositiveProgram_value_source_sameLaw
-- name    : OAI.ContingencyTables.CountingPositiveProgram.value_source_sameLaw
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:51:45.921867+00:00
-- url     : https://prove2.me/theorems/2635a289-5c26-4447-ac55-a5c8fa3b506d
-- title:
--   OAI.ContingencyTables.CountingPositiveProgram.value_source_sameLaw: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.CountingPositiveProgram.value_source_sameLaw` of [lean/OAI/Combinatorics/ContingencyTables/Counting/CountingHistoryApplication.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CountingHistoryApplication.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.CountingPositiveProgram`, with `open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication GridBoundary FiniteObservableTransport`, `open scoped Classical`):
--
--   ```lean
--   theorem value_source_sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
--       (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
--       (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0<epsilon) :
--       SameLaw
--         (fun bits : Fin (bitCount (CountingDirectProgram.request r c b epsilon delta))→Bool =>
--           TreeFraction.val (output (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
--         (RootedCountingWords.flatEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
--           (ComputedCountingWords.root hEK r c b hne epsilon he)
--           (ComputedCountingParameters.settings hEK r c b hne epsilon he))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContingencyTables.PublishedEdmondsKarp.EdmondsKarp1972Theorem1`, `OAI.ContingencyTables.TableTightening.Feasible`, `OAI.MatchingFPRAS.TreeFraction.Fraction` and `OAI.MatchingFPRAS.TreeFraction.val` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.CountingBaseProgram.Input` (definitions bundle `OAIQ089A004` of this split); `OAI.ContingencyTables.FiniteObservableTransport.SameLaw` (definitions bundle `OAIQ089A005` of this split); `OAI.ContingencyTables.ComputedCountingParameters.data`, `OAI.ContingencyTables.ComputedCountingParameters.settings`, `OAI.ContingencyTables.ComputedCountingWords.root`, `OAI.ContingencyTables.RootedCountingWords.bitCount` and `OAI.ContingencyTables.RootedCountingWords.flatEstimate` (definitions bundle `OAIQ089A006` of this split); `OAI.ContingencyTables.CountingDirectProgram.request` (definitions bundle `OAIQ089A007` of this split); `OAI.ContingencyTables.CountingPositiveProgram.bitCount` and `OAI.ContingencyTables.CountingPositiveProgram.output` (definitions bundle `OAIQ089A009` of this split).
--
--   **Used by.** The proof of `OAI.ContingencyTables.counting` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CountingHistoryApplication.lean (declaration OAI.ContingencyTables.CountingPositiveProgram.value_source_sameLaw)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009

section

attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

attribute [local irreducible] CountingPositiveProgram.output CompanionOuterHistoryProgram.output
  CompanionOuterPhaseProgram.output

theorem value_source_sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0<epsilon) :
    SameLaw
      (fun bits : Fin (bitCount (CountingDirectProgram.request r c b epsilon delta))→Bool =>
        TreeFraction.val (output (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
      (RootedCountingWords.flatEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (ComputedCountingWords.root hEK r c b hne epsilon he)
        (ComputedCountingParameters.settings hEK r c b hne epsilon he)) := by
  sorry

end
end ContingencyTables.CountingPositiveProgram

end OAI
end

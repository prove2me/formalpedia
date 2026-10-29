-- Prove2me | Theorems.Thm_OAI_ContingencyTables_CountingExecutedMachine_positive_success
-- name    : OAI.ContingencyTables.CountingExecutedMachine.positive_success
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:51:54.236988+00:00
-- url     : https://prove2.me/theorems/83469b2c-41c3-442a-9c1d-4345d747ff36
-- title:
--   OAI.ContingencyTables.CountingExecutedMachine.positive_success: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.CountingExecutedMachine.positive_success` of [lean/OAI/Combinatorics/ContingencyTables/Counting/CountingAmplifiedSourceLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CountingAmplifiedSourceLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.CountingExecutedMachine`, with `open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication GridBoundary FiniteObservableTransport`, `open scoped Classical`):
--
--   ```lean
--   theorem positive_success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
--       (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
--       (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k))
--       (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
--       (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
--       (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
--       (hp : 0<Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)))
--       (hs : SameLaw
--         (fun bits : Fin (CountingPositiveProgram.bitCount (CountingDirectProgram.request r c b epsilon delta))→Bool =>
--           TreeFraction.val (CountingPositiveProgram.output
--             (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
--         (RootedCountingWords.flatEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
--           (ComputedCountingWords.root hEK r c b hne epsilon he)
--           (ComputedCountingParameters.settings hEK r c b hne epsilon he))) :
--       1-(delta:ℝ) ≤ uniformAverage
--         (fun bits : Fin (positiveWidth (CountingDirectProgram.request r c b epsilon delta))→Bool =>
--           if CountingBranchProgram.Accurate r c b epsilon (TreeFraction.val (positive
--             (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits))) then (1:ℝ) else 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.uniformAverage` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.CompanionFactorialApplication.Labels`, `OAI.ContingencyTables.CompanionFactorialApplication.SmallCell`, `OAI.ContingencyTables.GridBoundary.Grid`, `OAI.ContingencyTables.PublishedEdmondsKarp.EdmondsKarp1972Theorem1`, `OAI.ContingencyTables.TableTightening.Feasible`, `OAI.MatchingFPRAS.TreeFraction.Fraction`, `OAI.MatchingFPRAS.TreeFraction.val` and `OAI.ContingencyTables.CompanionFactorialApplication.Instance` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.CountingBranchProgram.Accurate` (definitions bundle `OAIQ089A002` of this split); `OAI.ContingencyTables.CountingBaseProgram.Input`, `OAI.ContingencyTables.PublishedInputs.FiniteBoxPrekopaLeindler` and `OAI.ContingencyTables.PublishedInputs.FiniteCheeger` (definitions bundle `OAIQ089A004` of this split); `OAI.ContingencyTables.FiniteObservableTransport.SameLaw` (definitions bundle `OAIQ089A005` of this split); `OAI.ContingencyTables.ComputedCountingParameters.data`, `OAI.ContingencyTables.ComputedCountingParameters.settings`, `OAI.ContingencyTables.ComputedCountingWords.root`, `OAI.ContingencyTables.RootedCountingWords.bitCount` and `OAI.ContingencyTables.RootedCountingWords.flatEstimate` (definitions bundle `OAIQ089A006` of this split); `OAI.ContingencyTables.CountingDirectProgram.request` (definitions bundle `OAIQ089A007` of this split); `OAI.ContingencyTables.CountingExecutedMachine.positive`, `OAI.ContingencyTables.CountingExecutedMachine.positiveWidth`, `OAI.ContingencyTables.CountingPositiveProgram.bitCount` and `OAI.ContingencyTables.CountingPositiveProgram.output` (definitions bundle `OAIQ089A009` of this split); `OAI.ContingencyTables.BoundedTable` and `OAI.ContingencyTables.boundedTable_fintype` (the published bundle `Def_ContingencyTables`).
--
--   **Used by.** The proof of `OAI.ContingencyTables.counting` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CountingAmplifiedSourceLaw.lean (declaration OAI.ContingencyTables.CountingExecutedMachine.positive_success)

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
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem positive_success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k))
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
    (hp : 0<Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)))
    (hs : SameLaw
      (fun bits : Fin (CountingPositiveProgram.bitCount (CountingDirectProgram.request r c b epsilon delta))→Bool =>
        TreeFraction.val (CountingPositiveProgram.output
          (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
      (RootedCountingWords.flatEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (ComputedCountingWords.root hEK r c b hne epsilon he)
        (ComputedCountingParameters.settings hEK r c b hne epsilon he))) :
    1-(delta:ℝ) ≤ uniformAverage
      (fun bits : Fin (positiveWidth (CountingDirectProgram.request r c b epsilon delta))→Bool =>
        if CountingBranchProgram.Accurate r c b epsilon (TreeFraction.val (positive
          (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits))) then (1:ℝ) else 0) := by
  sorry

end
end ContingencyTables.CountingExecutedMachine

end OAI
end

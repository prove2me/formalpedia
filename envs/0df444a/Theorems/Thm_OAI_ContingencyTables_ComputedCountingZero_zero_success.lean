-- Prove2me | Theorems.Thm_OAI_ContingencyTables_ComputedCountingZero_zero_success
-- name    : OAI.ContingencyTables.ComputedCountingZero.zero_success
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T03:15:56.928008+00:00
-- url     : https://prove2.me/theorems/7148fe3d-3c42-407b-8e76-43fb84fcbc30
-- title:
--   OAI.ContingencyTables.ComputedCountingZero.zero_success: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.ComputedCountingZero.zero_success` of [lean/OAI/Combinatorics/ContingencyTables/Counting/ComputedCountingZero.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/ComputedCountingZero.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.ComputedCountingZero`, with `open CommonBasesFPRAS CompanionFactorialApplication GridBoundary`, `open CompanionOracleDensity CompanionTerminalApplication`, `open ComputedCountingParameters`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem zero_success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
--       (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
--       (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I:=Fin q) k))
--       (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
--       (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
--       (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
--       (hzero : Fintype.card (Labels (data hEK r c b hne epsilon he))=0) :
--       1-(delta:ℝ)≤uniformAverage (fun bits : Fin (zeroBits hEK r c b hne epsilon he delta)→Bool =>
--         if (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)≤
--             (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ) ∧
--           (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ)≤
--             (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
--         then (1:ℝ) else 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.uniformAverage` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.CompanionFactorialApplication.Labels`, `OAI.ContingencyTables.CompanionFactorialApplication.SmallCell`, `OAI.ContingencyTables.GridBoundary.Grid`, `OAI.ContingencyTables.PublishedEdmondsKarp.EdmondsKarp1972Theorem1`, `OAI.ContingencyTables.TableTightening.Feasible` and `OAI.ContingencyTables.CompanionFactorialApplication.Instance` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.PublishedInputs.FiniteBoxPrekopaLeindler` and `OAI.ContingencyTables.PublishedInputs.FiniteCheeger` (definitions bundle `OAIQ089A004` of this split); `OAI.ContingencyTables.ComputedCountingParameters.data`, `OAI.ContingencyTables.ComputedCountingZero.zeroBits` and `OAI.ContingencyTables.ComputedCountingZero.zeroEstimate` (definitions bundle `OAIQ089A006` of this split); `OAI.ContingencyTables.BoundedTable` and `OAI.ContingencyTables.boundedTable_fintype` (the published bundle `Def_ContingencyTables`).
--
--   **Used by.** The proof of `OAI.ContingencyTables.counting` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/ComputedCountingZero.lean (declaration OAI.ContingencyTables.ComputedCountingZero.zero_success)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A006

section

attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.ComputedCountingZero

open CommonBasesFPRAS CompanionFactorialApplication GridBoundary
open CompanionOracleDensity CompanionTerminalApplication
open ComputedCountingParameters
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

theorem zero_success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I:=Fin q) k))
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
    (hzero : Fintype.card (Labels (data hEK r c b hne epsilon he))=0) :
    1-(delta:ℝ)≤uniformAverage (fun bits : Fin (zeroBits hEK r c b hne epsilon he delta)→Bool =>
      if (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)≤
          (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ) ∧
        (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ)≤
          (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
      then (1:ℝ) else 0) := by
  sorry

end
end ContingencyTables.ComputedCountingZero

end OAI
end

-- Prove2me | Theorems.Thm_OAI_ContingencyTables_RootedHistoryConfidence_history_success
-- name    : OAI.ContingencyTables.RootedHistoryConfidence.history_success
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:03:58.449109+00:00
-- url     : https://prove2.me/theorems/7ab03e73-f3d9-4898-879c-660e5faa417d
-- title:
--   OAI.ContingencyTables.RootedHistoryConfidence.history_success: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.RootedHistoryConfidence.history_success` of [lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedHistoryConfidence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedHistoryConfidence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.RootedHistoryConfidence`, with `open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates`, `open CompanionOracleDensity RootedPhaseHistory RootedStoredHistory RootedHistoryStep`, `open CompanionTraceWords (eventIndicator)`, `open TwoLiftStates GridBoundary`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem history_success (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
--       (hC : 0 < s.C) (hB : (s.K:ℝ)=binWidth A s.C)
--       (hH : s.H ≤ rationalHeight A s.C)
--       (hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤ (2:ℝ)^s.L)
--       (hx0 : 0 < s.xi) (hx1 : s.xi ≤ 1/4)
--       (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
--       (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) s.K))
--       (hp : 0 < Fintype.card (Labels A)) (hn : 0 < s.n)
--       (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4) :
--       1-(s.H:ℝ)*error A s eta s.H ≤
--         uniformAverage (fun words : Fin s.H → Word A s =>
--           if GoodWords A R s eta (List.ofFn words) then (1:ℝ) else 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.uniformAverage` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.CompanionFactorialApplication.Instance`, `OAI.ContingencyTables.CompanionFactorialApplication.Labels`, `OAI.ContingencyTables.CompanionFactorialApplication.SmallCell`, `OAI.ContingencyTables.CompanionOracleDensity.binWidth`, `OAI.ContingencyTables.CompanionOracleDensity.dimension`, `OAI.ContingencyTables.CompanionOracleDensity.rationalHeight`, `OAI.ContingencyTables.GridBoundary.Grid`, `OAI.ContingencyTables.RootedCompletion.Selection` and `OAI.ContingencyTables.RootedPhaseHistory.Settings` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.PublishedInputs.FiniteBoxPrekopaLeindler` and `OAI.ContingencyTables.PublishedInputs.FiniteCheeger` (definitions bundle `OAIQ089A004` of this split); `OAI.ContingencyTables.RootedHistoryStep.error` (definitions bundle `OAIQ089A005` of this split); `OAI.ContingencyTables.RootedPhaseHistory.Word` and `OAI.ContingencyTables.RootedPhaseHistory.totalWidth` (definitions bundle `OAIQ089A006` of this split); `OAI.ContingencyTables.RootedHistoryConfidence.GoodWords` (definitions bundle `OAIQ089A009` of this split).
--
--   **Used by.** The proof of `OAI.ContingencyTables.CountingExecutedMachine.positive_success` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedHistoryConfidence.lean (declaration OAI.ContingencyTables.RootedHistoryConfidence.history_success)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009

section

attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.RootedHistoryConfidence

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedPhaseHistory RootedStoredHistory RootedHistoryStep
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

theorem history_success (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (hC : 0 < s.C) (hB : (s.K:ℝ)=binWidth A s.C)
    (hH : s.H ≤ rationalHeight A s.C)
    (hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤ (2:ℝ)^s.L)
    (hx0 : 0 < s.xi) (hx1 : s.xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) s.K))
    (hp : 0 < Fintype.card (Labels A)) (hn : 0 < s.n)
    (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4) :
    1-(s.H:ℝ)*error A s eta s.H ≤
      uniformAverage (fun words : Fin s.H → Word A s =>
        if GoodWords A R s eta (List.ofFn words) then (1:ℝ) else 0) := by
  sorry

end
end ContingencyTables.RootedHistoryConfidence

end OAI
end

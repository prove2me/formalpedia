-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQuerySetup_accepted
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:08:14.399282+00:00
-- url     : https://prove2.me/theorems/e7edae27-2b06-4866-aeb0-433196baaad0
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySetup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySetup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup`, with `open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram`, `open LeafProgram.Query HashGreedyProgram.NativeRound`, `open HighMarkedFrontend`):
--
--   ```lean
--   theorem accepted : ∃ C d : ℕ,
--       ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) (a : Data) (S B : ℕ),
--         q.Valid → CleanWork (project a) → Sources q (project a) → q.mark = none → q.index = [false] →
--         (∀ i, ¬H i → (a.stacks i).length ≤ S) →
--         (∀ i, H i → (a.stacks i).length ≤ B) →
--         (∀ i, (Circuit.result Serialization.code
--           (Execute.guardedModel (q.input k) (q.inputLengths k))).val i ≤ S) →
--         (∀ i, (Circuit.result Serialization.code
--           (Execute.guardedModel (q.input k) (q.inputLengths k))).len i ≤ S) →
--         let A := S + HighMarkedFrontend.acceptedBudget q k
--         let cost := C * (A+1)^d
--         ∃ nf front padding w,
--           Eval (HighMarkedFrontend.acceptedCommand k) nf a front ∧
--           nf + 1 ≤ HighMarkedFrontend.acceptedBudget q k ∧
--           FrontState q k (unmarkedInput (project a)) (project front) padding w ∧
--           ∃ run : PreparedRun q k hg front padding A B cost,
--             Eval (.seq (HighMarkedFrontend.acceptedCommand k)
--                 (.seq HighQueryProgram.prepare HighQueryProgram.seed))
--               (nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps)) a
--               (HighCountSeed.initialized (result front run.output) run.seedRegs) ∧
--             nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) ≤
--               HighMarkedFrontend.acceptedBudget q k + cost + 110 * localBound A cost + 81 ∧
--             (∀ i, HashMarkedReturn.kept i = true →
--               (HighCountSeed.initialized (result front run.output) run.seedRegs).stacks i = a.stacks i) ∧
--             StageSpace (.seq (HighMarkedFrontend.acceptedCommand k)
--               (.seq HighQueryProgram.prepare HighQueryProgram.seed))
--               (nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) + 1)
--               a (prefixBound q A cost B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.kept`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.localBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.words` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.result` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.unmarkedInput` (definitions bundle `OAIQ081S077` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.project` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.result` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.CleanWork` (definitions bundle `OAIQ081S127` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Sources` (definitions bundle `OAIQ081S146` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.code` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.inputLengths` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initialized`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.seed` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.prefixBound` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.Data` (definitions bundle `OAIQ081S173` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.FrontState` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.acceptedCommand` (definitions bundle `OAIQ081S183` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.acceptedBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.prepare` (definitions bundle `OAIQ081S186` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.arithmeticSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.packingSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.seedRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.seedSteps` (definitions bundle `OAIQ081S190` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySetup.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S190

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound
open HighMarkedFrontend

local notation "H" => (fun i : Fin 896 => i ∈ HighQueryProgram.Carried.words)

theorem accepted : ∃ C d : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) (a : Data) (S B : ℕ),
      q.Valid → CleanWork (project a) → Sources q (project a) → q.mark = none → q.index = [false] →
      (∀ i, ¬H i → (a.stacks i).length ≤ S) →
      (∀ i, H i → (a.stacks i).length ≤ B) →
      (∀ i, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).val i ≤ S) →
      (∀ i, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).len i ≤ S) →
      let A := S + HighMarkedFrontend.acceptedBudget q k
      let cost := C * (A+1)^d
      ∃ nf front padding w,
        Eval (HighMarkedFrontend.acceptedCommand k) nf a front ∧
        nf + 1 ≤ HighMarkedFrontend.acceptedBudget q k ∧
        FrontState q k (unmarkedInput (project a)) (project front) padding w ∧
        ∃ run : PreparedRun q k hg front padding A B cost,
          Eval (.seq (HighMarkedFrontend.acceptedCommand k)
              (.seq HighQueryProgram.prepare HighQueryProgram.seed))
            (nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps)) a
            (HighCountSeed.initialized (result front run.output) run.seedRegs) ∧
          nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) ≤
            HighMarkedFrontend.acceptedBudget q k + cost + 110 * localBound A cost + 81 ∧
          (∀ i, HashMarkedReturn.kept i = true →
            (HighCountSeed.initialized (result front run.output) run.seedRegs).stacks i = a.stacks i) ∧
          StageSpace (.seq (HighMarkedFrontend.acceptedCommand k)
            (.seq HighQueryProgram.prepare HighQueryProgram.seed))
            (nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) + 1)
            a (prefixBound q A cost B) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end

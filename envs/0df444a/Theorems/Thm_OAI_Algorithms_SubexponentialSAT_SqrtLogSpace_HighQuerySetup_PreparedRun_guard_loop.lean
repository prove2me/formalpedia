-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQuerySetup_PreparedRun_guard_loop
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.guard_loop
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T15:58:01.787201+00:00
-- url     : https://prove2.me/theorems/cf5296d9-032a-4702-9cd0-5cca81f4a3ba
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.guard_loop: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.guard_loop` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySetup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySetup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup`, with `open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram`, `open LeafProgram.Query HashGreedyProgram.NativeRound`, `open HighMarkedFrontend`):
--
--   ```lean
--   theorem PreparedRun.guard_loop {q k hg front padding S B cost}
--       (run : PreparedRun q k hg front padding S B cost) (last : Data) (steps K : ℕ)
--       (hloop : Eval HighQueryProgram.highLoop steps
--         (HighCountSeed.initialized (result front run.output) run.seedRegs) last)
--       (hspace : StageSpace HighQueryProgram.highLoop steps
--         (HighCountSeed.initialized (result front run.output) run.seedRegs) K) :
--       Eval HighQueryProgram.guardedCount
--         (run.packingSteps + run.arithmeticSteps + 1 + (run.seedSteps + steps) + 1) front last ∧
--         StageSpace HighQueryProgram.guardedCount
--           (run.packingSteps + run.arithmeticSteps + 1 + (run.seedSteps + steps) + 2) front
--           (max (prefixBound q S cost B) K)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.result` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initialized` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.prefixBound` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.Data` (definitions bundle `OAIQ081S173` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.arithmeticSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.packingSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.seedRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.seedSteps` (definitions bundle `OAIQ081S190` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.guardedCount` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.highLoop` (definitions bundle `OAIQ081S193` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySetup.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.guard_loop)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound
open HighMarkedFrontend

theorem PreparedRun.guard_loop {q k hg front padding S B cost}
    (run : PreparedRun q k hg front padding S B cost) (last : Data) (steps K : ℕ)
    (hloop : Eval HighQueryProgram.highLoop steps
      (HighCountSeed.initialized (result front run.output) run.seedRegs) last)
    (hspace : StageSpace HighQueryProgram.highLoop steps
      (HighCountSeed.initialized (result front run.output) run.seedRegs) K) :
    Eval HighQueryProgram.guardedCount
      (run.packingSteps + run.arithmeticSteps + 1 + (run.seedSteps + steps) + 1) front last ∧
      StageSpace HighQueryProgram.guardedCount
        (run.packingSteps + run.arithmeticSteps + 1 + (run.seedSteps + steps) + 2) front
        (max (prefixBound q S cost B) K) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end

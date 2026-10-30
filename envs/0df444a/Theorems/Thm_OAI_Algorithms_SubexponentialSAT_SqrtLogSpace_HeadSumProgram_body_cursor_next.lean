-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumProgram_body_cursor_next
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_cursor_next
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:36:10.783166+00:00
-- url     : https://prove2.me/theorems/94d58086-8ca1-45d1-863d-eb14f4480c47
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_cursor_next: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_cursor_next` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram`, with `open OAI BitProgram StructuredCalls CounterPrograms`, `open HeadEvaluationProgram.StagedGate (copy copyState clear clearState )`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing`, `open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram`, `open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram`):
--
--   ```lean
--   theorem body_cursor_next {h i : ℕ} {a b : Data} (hc : Cursor h i a)
--       (hp : 0 < value (a.stacks 860))
--       (hw : b.stacks 859 = a.stacks 859) (hf : b.stacks 860 = a.stacks 860)
--       (hs : b.stacks 861 = []) :
--       Cursor h (i + 1) (CounterForPrograms.nextState fuelPorts
--         (Counters.incrementResult cursorPorts b))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.nextState` (definitions bundle `OAIQ081S045` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters.incrementResult` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.cursorPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.fuelPorts` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Cursor` (definitions bundle `OAIQ081S165` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.Accumulator.advance` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_cursor_next)

import Mathlib
import Definitions.Def_OAIQ081S165

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

open HeadEvaluationProgram.StagedGate (copy copyState clear clearState )

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram

open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

theorem body_cursor_next {h i : ℕ} {a b : Data} (hc : Cursor h i a)
    (hp : 0 < value (a.stacks 860))
    (hw : b.stacks 859 = a.stacks 859) (hf : b.stacks 860 = a.stacks 860)
    (hs : b.stacks 861 = []) :
    Cursor h (i + 1) (CounterForPrograms.nextState fuelPorts
      (Counters.incrementResult cursorPorts b)) := by
  sorry

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end

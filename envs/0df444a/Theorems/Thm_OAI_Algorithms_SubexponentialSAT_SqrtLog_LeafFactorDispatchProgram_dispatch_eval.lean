-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram_dispatch_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.dispatch_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:09:30.335077+00:00
-- url     : https://prove2.me/theorems/45a561f9-030d-4a2b-9d56-bbb6c1d1ce14
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.dispatch_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.dispatch_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafFactorDispatchProgramChoose.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafFactorDispatchProgramChoose.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives`):
--
--   ```lean
--   theorem dispatch_eval (d : Data) (rows clauses : List (List Bool))
--       (hasMarked : Bool) (m f : ℕ)
--       (hrows : d.stacks 0=Encoding.encodeList id rows)
--       (hclauses : d.stacks 1=Encoding.encodeList id clauses)
--       (hcount : d.stacks 3=unary rows.length)
--       (hmark : hasMarked=true → d.stacks 4=Encoding.encodeNat m)
--       (hid : d.stacks 6=Encoding.encodeNat f)
--       (hflag : d.regs 7=hasMarked)
--       (hvalid : hasMarked=true → m < clauses.length)
--       (hc : FetchClean d) (ht : TestClean d) :
--       ∃ n e, n ≤ dispatchBound rows clauses m f ∧ Eval dispatch n d e ∧
--         Finished d e (decide (f < rows.length)) (hasMarked && decide (f=rows.length))
--           (selectedPayload rows clauses hasMarked m f)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.selectedPayload` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.unary` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.dispatchBound` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.dispatch` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.Data` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.FetchClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.Finished` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.TestClean` (definitions bundle `OAIQ081S107` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.dispatch_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.neutral_callback_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafFactorDispatchProgramChoose.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.dispatch_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S107

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem dispatch_eval (d : Data) (rows clauses : List (List Bool))
    (hasMarked : Bool) (m f : ℕ)
    (hrows : d.stacks 0=Encoding.encodeList id rows)
    (hclauses : d.stacks 1=Encoding.encodeList id clauses)
    (hcount : d.stacks 3=unary rows.length)
    (hmark : hasMarked=true → d.stacks 4=Encoding.encodeNat m)
    (hid : d.stacks 6=Encoding.encodeNat f)
    (hflag : d.regs 7=hasMarked)
    (hvalid : hasMarked=true → m < clauses.length)
    (hc : FetchClean d) (ht : TestClean d) :
    ∃ n e, n ≤ dispatchBound rows clauses m f ∧ Eval dispatch n d e ∧
      Finished d e (decide (f < rows.length)) (hasMarked && decide (f=rows.length))
        (selectedPayload rows clauses hasMarked m f) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

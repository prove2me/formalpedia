-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Steps_applyLoop_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.applyLoop_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:55:37.272736+00:00
-- url     : https://prove2.me/theorems/8d20a770-ac8e-483f-a443-5bacd12881dc
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.applyLoop_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.applyLoop_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramExecution.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramExecution.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps`, with `open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open HashCircuitProgram.Native`, `open MomentsProgram`):
--
--   ```lean
--   theorem applyLoop_eval (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
--       (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (vs : List (Triple (RingProgram.ScalarCode p t))) (regs : Regs) (high : Data)
--       (hh : high 12=Product.bytes h) (hg : high 30=Product.bytes g)
--       (htape : high 22=triplesTape vs) (h5 : high 5=[]) (h23 : high 23=[])
--       (h28 : high 28=[]) (h29 : high 29=[]) (h31 : high 31=[])
--       (hshape : (high 32).length=n) (hready : scalarReady 11 high) :
--       ∃ cost ≤ applyLoopCost ctx h g vs (high 38), ∃ rr,
--         Eval applyLoop cost (Memory.state regs (low ctx) high)
--           (Memory.state rr (low ctx)
--             (Function.update (Function.update (Function.update high 30 []) 38 []) 11
--               (Product.bytes (loopResult ctx h g vs.reverse []))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Triple`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Regs` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.scalarReady` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory.state` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.triplesTape` (definitions bundle `OAIQ081S103` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.applyLoop` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Raw`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.applyLoopCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.loopResult` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.low` (definitions bundle `OAIQ081S139` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramExecution.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.applyLoop_eval)

import Mathlib
import Definitions.Def_OAIQ081S139

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem applyLoop_eval (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
    (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) (regs : Regs) (high : Data)
    (hh : high 12=Product.bytes h) (hg : high 30=Product.bytes g)
    (htape : high 22=triplesTape vs) (h5 : high 5=[]) (h23 : high 23=[])
    (h28 : high 28=[]) (h29 : high 29=[]) (h31 : high 31=[])
    (hshape : (high 32).length=n) (hready : scalarReady 11 high) :
    ∃ cost ≤ applyLoopCost ctx h g vs (high 38), ∃ rr,
      Eval applyLoop cost (Memory.state regs (low ctx) high)
        (Memory.state rr (low ctx)
          (Function.update (Function.update (Function.update high 30 []) 38 []) 11
            (Product.bytes (loopResult ctx h g vs.reverse [])))) := by
  sorry

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

end OAI.Algorithms
end

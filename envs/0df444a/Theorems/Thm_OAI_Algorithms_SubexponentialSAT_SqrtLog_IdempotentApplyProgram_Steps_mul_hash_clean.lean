-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Steps_mul_hash_clean
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.mul_hash_clean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:56:20.016342+00:00
-- url     : https://prove2.me/theorems/bdd1a4b4-f541-489e-a75a-17209aab9999
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.mul_hash_clean: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.mul_hash_clean` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramExecution.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramExecution.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps`, with `open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open HashCircuitProgram.Native`, `open MomentsProgram`):
--
--   ```lean
--   theorem mul_hash_clean (c : Context p t n d) (a h : Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (regs : Regs) (high : Data) (ha : high 11=Product.bytes a)
--       (hh : high 12=Product.bytes h) (hempty : high 5=[]) (htmp : high 14=[]) :
--       ∃ cost ≤ 7*(Product.bytes h).length+5+mulCost c a h, ∃ rr,
--         Eval (.seq (copy 68 61 70) (productAdapter product)) cost
--           (Memory.state regs (low c) high)
--           (Memory.state rr (low c) (Function.update high 11 (Product.bytes (mul c a h))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Regs` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.copy` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.productAdapter` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.product` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory.state` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Raw`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.low`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.mul` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.mulCost` (definitions bundle `OAIQ081S139` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.loop_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramExecution.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.mul_hash_clean)

import Mathlib
import Definitions.Def_OAIQ081S139

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram
namespace Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem mul_hash_clean (c : Context p t n d) (a h : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (regs : Regs) (high : Data) (ha : high 11=Product.bytes a)
    (hh : high 12=Product.bytes h) (hempty : high 5=[]) (htmp : high 14=[]) :
    ∃ cost ≤ 7*(Product.bytes h).length+5+mulCost c a h, ∃ rr,
      Eval (.seq (copy 68 61 70) (productAdapter product)) cost
        (Memory.state regs (low c) high)
        (Memory.state rr (low c) (Function.update high 11 (Product.bytes (mul c a h)))) := by
  sorry

end Steps
end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

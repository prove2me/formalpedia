-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_earlyCall_eval_bounded
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.earlyCall_eval_bounded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:51:29.643599+00:00
-- url     : https://prove2.me/theorems/82cba2df-e9a1-4661-8db7-30aafe130564
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.earlyCall_eval_bounded: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.earlyCall_eval_bounded` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendEarlyBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendEarlyBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend`, with `open SubexponentialSAT BitProgram StructuredCalls`):
--
--   ```lean
--   theorem earlyCall_eval_bounded (a : Data) (ambient : List Bool)
--       (hp : projectState r8 early a=LeafParametersProgram.Bank.state (a.regs ∘ r8)
--         (EarlyThreshold.inputWords ambient)) :
--       ∃ n ≤ EarlyThreshold.runtimeBound ambient, ∃ rf w,
--         Eval earlyCall n a (embedState r8 early a (LeafParametersProgram.Bank.state rf w)) ∧
--         BinaryArithmetic.toNat (w 16)=EarlyThreshold.threshold (BinaryArithmetic.toNat ambient) ∧
--         w 0=ambient ∧ (∀ j, j≠0 → j≠13 → j≠16 → w j=[]) ∧
--         (w 16).length ≤ Asymptotic.L (BinaryArithmetic.toNat ambient)+1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.L` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Regs` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.early` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.r8` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` and `OAI.Algorithms.SubexponentialSAT.StructuredCalls.embedState` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.threshold` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.runtimeBound` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.state` (definitions bundle `OAIQ081S083` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Data` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.inputWords` (definitions bundle `OAIQ081S102` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.earlyCall` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCommand_eval_bounded` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendEarlyBound.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.earlyCall_eval_bounded)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S169

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem earlyCall_eval_bounded (a : Data) (ambient : List Bool)
    (hp : projectState r8 early a=LeafParametersProgram.Bank.state (a.regs ∘ r8)
      (EarlyThreshold.inputWords ambient)) :
    ∃ n ≤ EarlyThreshold.runtimeBound ambient, ∃ rf w,
      Eval earlyCall n a (embedState r8 early a (LeafParametersProgram.Bank.state rf w)) ∧
      BinaryArithmetic.toNat (w 16)=EarlyThreshold.threshold (BinaryArithmetic.toNat ambient) ∧
      w 0=ambient ∧ (∀ j, j≠0 → j≠13 → j≠16 → w j=[]) ∧
      (w 16).length ≤ Asymptotic.L (BinaryArithmetic.toNat ambient)+1 := by
  sorry

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

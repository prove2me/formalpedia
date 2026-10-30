-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_Interval_at_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.at_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:03:02.263977+00:00
-- url     : https://prove2.me/theorems/11e47fa8-1e8f-4768-b690-c503170312b3
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.at_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.at_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramInterval.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramInterval.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval`, with `open BitProgram StructuredCalls BinaryArithmetic Bank Circuit`):
--
--   ```lean
--   theorem at_eval (r : Regs) (w : Words)
--       (hc : ∀ a : Fin 64, 46 ≤ a.val → w a=[])
--       (hr : 0 < BinaryArithmetic.toNat (w 18)) :
--       ∃ t rf word, Eval intervalAt t (Bank.state r w)
--           (Bank.state rf (Function.update w 46 word)) ∧
--         BinaryArithmetic.toNat word=Subexp.TailInterval.intervalStart
--           (BinaryArithmetic.toNat (w 18)) (BinaryArithmetic.toNat (w 21)) (BinaryArithmetic.toNat (w 29)) ∧
--         word.length ≤ 4*((w 18).length+(w 21).length+(w 29).length+1) ∧
--         t ≤ 10000*((w 18).length+(w 21).length+(w 29).length+1)^2+1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Regs` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.state` (definitions bundle `OAIQ081S083` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.intervalAt` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cacheCall_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramInterval.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.at_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S092

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem at_eval (r : Regs) (w : Words)
    (hc : ∀ a : Fin 64, 46 ≤ a.val → w a=[])
    (hr : 0 < BinaryArithmetic.toNat (w 18)) :
    ∃ t rf word, Eval intervalAt t (Bank.state r w)
        (Bank.state rf (Function.update w 46 word)) ∧
      BinaryArithmetic.toNat word=Subexp.TailInterval.intervalStart
        (BinaryArithmetic.toNat (w 18)) (BinaryArithmetic.toNat (w 21)) (BinaryArithmetic.toNat (w 29)) ∧
      word.length ≤ 4*((w 18).length+(w 21).length+(w 29).length+1) ∧
      t ≤ 10000*((w 18).length+(w 21).length+(w 29).length+1)^2+1 := by
  sorry

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval

end OAI.Algorithms
end

-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_appendSlot_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendSlot_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:23:34.327994+00:00
-- url     : https://prove2.me/theorems/7c536f6c-2c66-45a3-aada-992da0c56f6b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendSlot_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendSlot_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramAppend.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramAppend.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic`):
--
--   ```lean
--   theorem appendSlot_eval (d : Data)
--       (h22 : d.stacks 22=[]) (h23 : d.stacks 23=[])
--       (h24 : d.stacks 24=[]) (h25 : d.stacks 25=[])
--       (hw : ∀ i, d.stacks (arithmeticWork i)=[])
--       (hv : BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d) < 2^(d.stacks 5).length) :
--       ∃ n rf, Eval appendSlot n d
--         ⟨rf,Function.update d.stacks 13
--           ((SubexpLiftRing.fixedBits (d.stacks 5).length
--             (BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d))).reverse++d.stacks 13)⟩ ∧
--         n ≤ appendCost d ∧ (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.fixedBits` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.arithmeticWork` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Data` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendSlot` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.offsetWord` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStep_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramAppend.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendSlot_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S118

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem appendSlot_eval (d : Data)
    (h22 : d.stacks 22=[]) (h23 : d.stacks 23=[])
    (h24 : d.stacks 24=[]) (h25 : d.stacks 25=[])
    (hw : ∀ i, d.stacks (arithmeticWork i)=[])
    (hv : BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d) < 2^(d.stacks 5).length) :
    ∃ n rf, Eval appendSlot n d
      ⟨rf,Function.update d.stacks 13
        ((SubexpLiftRing.fixedBits (d.stacks 5).length
          (BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d))).reverse++d.stacks 13)⟩ ∧
      n ≤ appendCost d ∧ (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  sorry

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

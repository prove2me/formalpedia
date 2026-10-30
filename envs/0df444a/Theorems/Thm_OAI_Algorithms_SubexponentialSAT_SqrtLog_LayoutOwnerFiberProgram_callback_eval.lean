-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgram_callback_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.callback_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:01:22.044402+00:00
-- url     : https://prove2.me/theorems/03cce811-ca1b-4c0c-97f7-86c71d7e4c9c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.callback_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.callback_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutOwnerFiberProgramVisit.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutOwnerFiberProgramVisit.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives`):
--
--   ```lean
--   theorem callback_eval (regs : Fin 5 → Bool) (query index count : ℕ)
--       (v f : ℕ) (master tail acc out : List Bool) :
--       ∃ n ≤ callbackCost query index (v,f), ∃ rr,
--         Eval callback n
--           (data regs (unary query) master tail (pairPayload v f).reverse [] [] []
--             (unary index) acc (unary count) out)
--           (data (reset rr) (unary query) master tail [] [] [] [] (unary (index+1))
--             (if v=query then (Encoding.encodeNat index).reverse++acc else acc)
--             (unary (count+(if v=query then 1 else 0))) out)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.callbackCost` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.unary` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.reset` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.callback` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.pairPayload` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.data` (definitions bundle `OAIQ081S089` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.query_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.findOwner_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutOwnerFiberProgramVisit.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.callback_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S089

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem callback_eval (regs : Fin 5 → Bool) (query index count : ℕ)
    (v f : ℕ) (master tail acc out : List Bool) :
    ∃ n ≤ callbackCost query index (v,f), ∃ rr,
      Eval callback n
        (data regs (unary query) master tail (pairPayload v f).reverse [] [] []
          (unary index) acc (unary count) out)
        (data (reset rr) (unary query) master tail [] [] [] [] (unary (index+1))
          (if v=query then (Encoding.encodeNat index).reverse++acc else acc)
          (unary (count+(if v=query then 1 else 0))) out) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

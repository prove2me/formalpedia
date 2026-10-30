-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram_hashBranch_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.hashBranch_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:09:34.562053+00:00
-- url     : https://prove2.me/theorems/10c5e32d-ee52-4ea1-8ccc-a942586a86f9
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.hashBranch_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.hashBranch_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafFactorDispatchProgramBranches.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafFactorDispatchProgramBranches.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives`):
--
--   ```lean
--   theorem hashBranch_eval (d : Data) (rows : List (List Bool)) (i : Fin rows.length)
--       (hm : d.stacks 0=Encoding.encodeList id rows) (hi : d.stacks 6=Encoding.encodeNat i.val)
--       (hc : FetchClean d) :
--       ∃ n e, n ≤ 23*(Encoding.encodeList id rows).length+21 ∧ Eval hashBranch n d e ∧
--         Finished d e true false rows[i.val]
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.hashBranch` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.Data` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.FetchClean` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.Finished` (definitions bundle `OAIQ081S107` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.dispatch_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafFactorDispatchProgramBranches.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.hashBranch_eval)

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

theorem hashBranch_eval (d : Data) (rows : List (List Bool)) (i : Fin rows.length)
    (hm : d.stacks 0=Encoding.encodeList id rows) (hi : d.stacks 6=Encoding.encodeNat i.val)
    (hc : FetchClean d) :
    ∃ n e, n ≤ 23*(Encoding.encodeList id rows).length+21 ∧ Eval hashBranch n d e ∧
      Finished d e true false rows[i.val] := by
  sorry

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

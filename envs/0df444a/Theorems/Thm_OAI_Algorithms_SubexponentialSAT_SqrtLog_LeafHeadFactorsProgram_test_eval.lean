-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadFactorsProgram_test_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.test_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:01:17.787993+00:00
-- url     : https://prove2.me/theorems/9fad8f76-795a-456d-8145-ca767ef5c20c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.test_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.test_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHeadFactorsProgramTest.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHeadFactorsProgramTest.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives`):
--
--   ```lean
--   theorem test_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
--       (hs : d.stacks 33 = earlier.flatten ++ (word ++ rest))
--       (hi : (d.stacks 31).length + (d.stacks 39).length = earlier.length)
--       (hw : word.length = (d.stacks 38).length)
--       (hr : ∀ row ∈ earlier, row.length = (d.stacks 38).length) (hc : Clean d) :
--       Eval test (testCost (d.stacks 31).length (d.stacks 39).length
--         (d.stacks 38).length (d.stacks 32) word)
--         d (tested d (word.getD (d.stacks 32).length false))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.testCost` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.Clean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.tested` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.test` (definitions bundle `OAIQ081S144` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.factors_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHeadFactorsProgramTest.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.test_eval)

import Mathlib
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem test_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
    (hs : d.stacks 33 = earlier.flatten ++ (word ++ rest))
    (hi : (d.stacks 31).length + (d.stacks 39).length = earlier.length)
    (hw : word.length = (d.stacks 38).length)
    (hr : ∀ row ∈ earlier, row.length = (d.stacks 38).length) (hc : Clean d) :
    Eval test (testCost (d.stacks 31).length (d.stacks 39).length
      (d.stacks 38).length (d.stacks 32) word)
      d (tested d (word.getD (d.stacks 32).length false)) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

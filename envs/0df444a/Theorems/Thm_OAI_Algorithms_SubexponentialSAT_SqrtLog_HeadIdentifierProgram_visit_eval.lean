-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HeadIdentifierProgram_visit_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visit_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:29:16.01469+00:00
-- url     : https://prove2.me/theorems/4eab1d75-818b-490a-aba4-46f157e4c106
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visit_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visit_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HeadIdentifierProgramVisit.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HeadIdentifierProgramVisit.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives`):
--
--   ```lean
--   theorem visit_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool) (j : ℕ)
--       (hs : d.stacks 33=earlier.flatten++(word++rest)) (hj : d.stacks 39=unary j)
--       (hi : j=earlier.length) (hw : word.length=(d.stacks 38).length)
--       (hr : ∀ row ∈ earlier,row.length=(d.stacks 38).length) (hc : Clean d) :
--       ∃ ticks e, ticks ≤ visitBound j (d.stacks 38).length (d.stacks 31).length (d.stacks 32).length ∧
--         Eval visit ticks d e ∧
--         e.stacks=Function.update (Function.update d.stacks 0
--           (if (d.stacks 31).getD j false && word.getD (d.stacks 32).length false
--             then record j++d.stacks 0 else d.stacks 0))
--           1 (if (d.stacks 31).getD j false && word.getD (d.stacks 32).length false
--             then false::d.stacks 1 else d.stacks 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.unary` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visitBound` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.record` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.Data` (definitions bundle `OAIQ081S102` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.Clean` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visit` (definitions bundle `OAIQ081S119` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.heads_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HeadIdentifierProgramVisit.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visit_eval)

import Mathlib
import Definitions.Def_OAIQ081S119

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem visit_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool) (j : ℕ)
    (hs : d.stacks 33=earlier.flatten++(word++rest)) (hj : d.stacks 39=unary j)
    (hi : j=earlier.length) (hw : word.length=(d.stacks 38).length)
    (hr : ∀ row ∈ earlier,row.length=(d.stacks 38).length) (hc : Clean d) :
    ∃ ticks e, ticks ≤ visitBound j (d.stacks 38).length (d.stacks 31).length (d.stacks 32).length ∧
      Eval visit ticks d e ∧
      e.stacks=Function.update (Function.update d.stacks 0
        (if (d.stacks 31).getD j false && word.getD (d.stacks 32).length false
          then record j++d.stacks 0 else d.stacks 0))
        1 (if (d.stacks 31).getD j false && word.getD (d.stacks 32).length false
          then false::d.stacks 1 else d.stacks 1) := by
  sorry

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

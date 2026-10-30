-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram_StagedGate_bodyBudget_uniform
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.bodyBudget_uniform
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:47:03.796348+00:00
-- url     : https://prove2.me/theorems/f423ae98-4a59-4dd9-95e4-39676b736ff6
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.bodyBudget_uniform: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.bodyBudget_uniform` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadEvaluationProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadEvaluationProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate`, with `open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram`):
--
--   ```lean
--   theorem bodyBudget_uniform (a : Data) (rows : List (List (List Bool))) (B acceptedCost : ℕ)
--       (hmatrix : a.stacks 865=words (rows.map words))
--       (hlen : ∀ row ∈ rows,row.length=(a.stacks 859).length)
--       (hwidth : ∀ row ∈ rows,∀ x ∈ row,x.length≤B)
--       (hrows : rows.length≤B) (ha : ∀ i, (a.stacks i).length≤B) :
--       HeadGate.budget (a.stacks 864) (a.stacks 859) rows (a.stacks 866)+
--         9*sourceLength a+acceptedCost+8*(a.stacks 859).length+58≤
--         bodyPolynomial B+acceptedCost
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.bodyPolynomial` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate.budget` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.sourceLength` (definitions bundle `OAIQ081S136` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadEvaluationProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.bodyBudget_uniform)

import Mathlib
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

theorem bodyBudget_uniform (a : Data) (rows : List (List (List Bool))) (B acceptedCost : ℕ)
    (hmatrix : a.stacks 865=words (rows.map words))
    (hlen : ∀ row ∈ rows,row.length=(a.stacks 859).length)
    (hwidth : ∀ row ∈ rows,∀ x ∈ row,x.length≤B)
    (hrows : rows.length≤B) (ha : ∀ i, (a.stacks i).length≤B) :
    HeadGate.budget (a.stacks 864) (a.stacks 859) rows (a.stacks 866)+
      9*sourceLength a+acceptedCost+8*(a.stacks 859).length+58≤
      bodyPolynomial B+acceptedCost := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
end

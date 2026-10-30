-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorLoadBounds_generated_bounds
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.generated_bounds
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:21:00.57601+00:00
-- url     : https://prove2.me/theorems/e273030a-047c-45f5-b29b-e4a34a0b648b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.generated_bounds: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.generated_bounds` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorLoadBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorLoadBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport`):
--
--   ```lean
--   theorem generated_bounds (s : LeafHeadSetupProgram.Native.Inputs) (z L : ℕ)
--       (W bits : List Bool) (raw : List (List LayoutMatrixProgram.Pair))
--       (ys : List (List (List Bool)))
--       (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
--         (LeafHeadSetupProgram.selectedHeads s.n s.rows s.low z) raw)
--       (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys)
--       (hW : W.length ≤ L)
--       (hbits : bits.length=(LeafHeadSetupProgram.selectedHeads s.n s.rows s.low z).length) :
--       (words (ys.map words)).length ≤ matrixEnvelope s L ∧
--         (∀ row ∈ ys,∀ x ∈ row,x.length ≤ matrixEnvelope s L) ∧
--         16*(W.length+bits.length+(words (ys.map words)).length)+
--           AttainedSignatureProgram.cost W bits ys+1 ≤ keyEnvelope s L
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.SignedWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Pair` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.selectedHeads` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.shiftedWord` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.MatrixRel` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.cost` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.relation` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.columnLength` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.keyEnvelope` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.matrixEnvelope` (definitions bundle `OAIQ081S179` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.evaluateHead_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorLoadBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.generated_bounds)

import Mathlib
import Definitions.Def_OAIQ081S179

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

theorem generated_bounds (s : LeafHeadSetupProgram.Native.Inputs) (z L : ℕ)
    (W bits : List Bool) (raw : List (List LayoutMatrixProgram.Pair))
    (ys : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (LeafHeadSetupProgram.selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys)
    (hW : W.length ≤ L)
    (hbits : bits.length=(LeafHeadSetupProgram.selectedHeads s.n s.rows s.low z).length) :
    (words (ys.map words)).length ≤ matrixEnvelope s L ∧
      (∀ row ∈ ys,∀ x ∈ row,x.length ≤ matrixEnvelope s L) ∧
      16*(W.length+bits.length+(words (ys.map words)).length)+
        AttainedSignatureProgram.cost W bits ys+1 ≤ keyEnvelope s L := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds
end

-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_scanner_caps_polynomial
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.scanner_caps_polynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:01:06.579324+00:00
-- url     : https://prove2.me/theorems/3ae9a0bd-2888-4b55-92c1-75ad6dd3aab4
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.scanner_caps_polynomial: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.scanner_caps_polynomial` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleLoader.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleLoader.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open SignatureTupleProgram SignatureTupleNative`, `open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage`, `open SignatureTupleDFS SignatureTupleTraversal`):
--
--   ```lean
--   theorem scanner_caps_polynomial (s : Native.Inputs) (source : Data) (B z : ℕ)
--       (ha : Native.Ready s source) (hB : WordBound B source) (W : List Bool) (hW : W.length≤B)
--       (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
--       (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
--         (selectedHeads s.n s.rows s.low z) raw)
--       (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted) :
--       let h := (selectedHeads s.n s.rows s.low z).length
--       let C := 3*(s.columnLength+B)+1
--       AttainedSignatureProgram.Rescan.polynomialBudget W shifted h C ≤ scannerEnvelope B ∧
--         AttainedSignatureProgram.Rescan.spaceBudget W shifted h C ≤ scannerEnvelope B ∧
--         AttainedSignatureProgram.Rescan.keyBound W h shifted.length C ≤ scannerEnvelope B
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.SignedWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Pair` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.selectedHeads` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.scannerEnvelope` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.shiftedWord` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.keyBound` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.MatrixRel` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.polynomialBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.spaceBudget` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.relation` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Ready` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.columnLength` (definitions bundle `OAIQ081S168` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.duplicate_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.fresh_internal_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.nonleaf_iteration_masterFrame` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleLoader.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.scanner_caps_polynomial)

import Mathlib
import Definitions.Def_OAIQ081S168

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

section Storage
open SignatureTupleDFS SignatureTupleTraversal

theorem scanner_caps_polynomial (s : Native.Inputs) (source : Data) (B z : ℕ)
    (ha : Native.Ready s source) (hB : WordBound B source) (W : List Bool) (hW : W.length≤B)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted) :
    let h := (selectedHeads s.n s.rows s.low z).length
    let C := 3*(s.columnLength+B)+1
    AttainedSignatureProgram.Rescan.polynomialBudget W shifted h C ≤ scannerEnvelope B ∧
      AttainedSignatureProgram.Rescan.spaceBudget W shifted h C ≤ scannerEnvelope B ∧
      AttainedSignatureProgram.Rescan.keyBound W h shifted.length C ≤ scannerEnvelope B := by
  sorry

end Storage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

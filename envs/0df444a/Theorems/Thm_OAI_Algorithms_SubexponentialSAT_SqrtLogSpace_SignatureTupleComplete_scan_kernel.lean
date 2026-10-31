-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_scan_kernel
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.scan_kernel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:21:46.073194+00:00
-- url     : https://prove2.me/theorems/a7189fc4-92e8-43f9-8ea1-a8a43e37f143
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.scan_kernel: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.scan_kernel` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleComplete.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleComplete.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete`, with `open Classical`, `open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing`, `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage`, `open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram`, `open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource`):
--
--   ```lean
--   theorem scan_kernel (s : ProducedSource) (depth : ℕ)
--       (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
--       (hr : LayoutMatrixProgram.MatrixRel s.input.relation s.input.columnLength s.input.D
--         (selectedHeads s.input.n s.input.rows s.input.low (s.base+depth)) raw)
--       (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (s.source.stacks 141))) raw shifted)
--       (i j : Fin (2^s.headSize depth)) :
--       AttainedSignatureProgram.Rescan.naturalKey (s.source.stacks 141) shifted (s.headSize depth) i=
--         AttainedSignatureProgram.Rescan.naturalKey (s.source.stacks 141) shifted (s.headSize depth) j ↔
--         s.key depth i=s.key depth j
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.SignedWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Pair` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.selectedHeads` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.shiftedWord` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.MatrixRel` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.relation` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.columnLength` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.base`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.headSize` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.key` (definitions bundle `OAIQ081S178` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.duplicate_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.fresh_internal_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.nonleaf_iteration_masterFrame` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleComplete.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.scan_kernel)

import Mathlib
import Definitions.Def_OAIQ081S178

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource

theorem scan_kernel (s : ProducedSource) (depth : ℕ)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.input.relation s.input.columnLength s.input.D
      (selectedHeads s.input.n s.input.rows s.input.low (s.base+depth)) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (s.source.stacks 141))) raw shifted)
    (i j : Fin (2^s.headSize depth)) :
    AttainedSignatureProgram.Rescan.naturalKey (s.source.stacks 141) shifted (s.headSize depth) i=
      AttainedSignatureProgram.Rescan.naturalKey (s.source.stacks 141) shifted (s.headSize depth) j ↔
      s.key depth i=s.key depth j := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

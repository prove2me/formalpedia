-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_ascend_native_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.ascend_native_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:21:35.225213+00:00
-- url     : https://prove2.me/theorems/5c3fab20-1221-48aa-84db-7efffb12e81a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.ascend_native_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.ascend_native_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleLoader.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleLoader.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement`, `open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage`, `open SignatureTupleDFS SignatureTupleTraversal`):
--
--   ```lean
--   theorem ascend_native_run (h : ℕ → ℕ) {κ : ℕ → Type*}
--       (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ) (depth : Fin levels)
--       (ancestors : Prefix (Representatives key) (depth.val+1))
--       (s : Native.Inputs) (source : Data) (ha : Native.Ready s source)
--       (B : ℕ) (hB : WordBound B source) (hrows : s.rows.length=s.n+s.N)
--       (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
--       (hw : CacheCorrect s.height (unary s.R) s.width words)
--       (a : State 40 896)
--       (hm : SignatureHeadLoader.MasterFrame (Native.start s source ra rd rc words)
--         (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
--       (hanc : AncestorStorage h key levels base (depth.val+1) ancestors a)
--       (F L hmax : ℕ) (hf : WordBound F a) (hW : (a.stacks 141).length≤L)
--       (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F)
--       (hh : ∀ d<levels,h d≤hmax)
--       (hcap : 6*levels*(hmax+1)+(base+levels)+(hmax+1)≤F)
--       (hsize : (selectedHeads s.n s.rows s.low (base+depth.val)).length=h depth.val) :
--       ∃ rp rm rs raw shifted total,
--         let loaded := result s (base+depth.val) (parentReturnState h key depth.val ancestors a)
--           rp rm rs raw shifted
--         let finish := advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) loaded)
--         Eval (ascendWith loadHead) total a finish ∧
--         total+1 ≤ runEnvelope B F+69*F+100 ∧ WordBound F finish ∧
--         ScanStorage h key levels base depth (Fin.init ancestors)
--           ((ancestors (Fin.last depth.val)).val.val+1) finish ∧
--         (∀ hn : (ancestors (Fin.last depth.val)).val.val+1<2^h depth.val,
--           CandidateReady finish (a.stacks 141) shifted (h depth.val) ⟨_,hn⟩) ∧
--         LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
--           (selectedHeads s.n s.rows s.low (base+depth.val)) raw ∧
--         List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) raw shifted ∧
--         ∀ prefixSteps intermediate, prefixSteps≤total+1 →
--           Trace (compiled (ascendWith loadHead) 0 0) prefixSteps
--             (a.withPC (some (compiled (ascendWith loadHead) 0 0).entry)) intermediate →
--           ∀ i,(intermediate.stacks i).length≤2000*(F+1)+runEnvelope B F
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.SignedWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Pair` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.selectedHeads` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.lowStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.retainedOutputBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS.Prefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.runEnvelope` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.tupleStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.shiftedWord` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal.Representatives` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.MatrixRel` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.CacheCorrect` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.relation` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Ready` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.ascendWith` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.MasterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.AncestorStorage`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.CandidateReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.copyState` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.parentReturnState` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.ScanStorage` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.advanceCandidateState` (definitions bundle `OAIQ081S152` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.result` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.columnLength` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.loadHead` (definitions bundle `OAIQ081S191` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.ascend_leaf` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.exhausted_successor_step` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleLoader.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.ascend_native_run)

import Mathlib
import Definitions.Def_OAIQ081S191

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

section Storage
open SignatureTupleDFS SignatureTupleTraversal

theorem ascend_native_run (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) (depth.val+1))
    (s : Native.Inputs) (source : Data) (ha : Native.Ready s source)
    (B : ℕ) (hB : WordBound B source) (hrows : s.rows.length=s.n+s.N)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s source ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hanc : AncestorStorage h key levels base (depth.val+1) ancestors a)
    (F L hmax : ℕ) (hf : WordBound F a) (hW : (a.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F)
    (hh : ∀ d<levels,h d≤hmax)
    (hcap : 6*levels*(hmax+1)+(base+levels)+(hmax+1)≤F)
    (hsize : (selectedHeads s.n s.rows s.low (base+depth.val)).length=h depth.val) :
    ∃ rp rm rs raw shifted total,
      let loaded := result s (base+depth.val) (parentReturnState h key depth.val ancestors a)
        rp rm rs raw shifted
      let finish := advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) loaded)
      Eval (ascendWith loadHead) total a finish ∧
      total+1 ≤ runEnvelope B F+69*F+100 ∧ WordBound F finish ∧
      ScanStorage h key levels base depth (Fin.init ancestors)
        ((ancestors (Fin.last depth.val)).val.val+1) finish ∧
      (∀ hn : (ancestors (Fin.last depth.val)).val.val+1<2^h depth.val,
        CandidateReady finish (a.stacks 141) shifted (h depth.val) ⟨_,hn⟩) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low (base+depth.val)) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total+1 →
        Trace (compiled (ascendWith loadHead) 0 0) prefixSteps
          (a.withPC (some (compiled (ascendWith loadHead) 0 0).entry)) intermediate →
        ∀ i,(intermediate.stacks i).length≤2000*(F+1)+runEnvelope B F := by
  sorry

end Storage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

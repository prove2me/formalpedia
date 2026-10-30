-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_setup_native_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.setup_native_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:23:03.761647+00:00
-- url     : https://prove2.me/theorems/72ac34dc-8640-42e4-9aca-d58b62335090
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.setup_native_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.setup_native_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleLoader.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleLoader.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement`, `open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage`, `open SignatureTupleDFS SignatureTupleTraversal`):
--
--   ```lean
--   theorem setup_native_run (s : Native.Inputs) (source : Data) (ha : Native.Ready s source)
--       (B : ℕ) (hB : WordBound B source) (hrows : s.rows.length=s.n+s.N)
--       (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
--       (hw : CacheCorrect s.height (unary s.R) s.width words)
--       (a : State 40 896)
--       (hm : SignatureHeadLoader.MasterFrame (Native.start s source ra rd rc words)
--         (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
--       (base F L : ℕ) (hbase : a.stacks 649=unary base) (hpositive : 0 < s.r)
--       (hf : WordBound F a) (hW : (a.stacks 141).length≤L)
--       (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F) :
--       ∃ rp rm rs raw shifted total,
--         Eval (setupWith loadHead) total a
--           (resetGeneratorState (result s base (initialControlState a) rp rm rs raw shifted)) ∧
--         total+1 ≤ runEnvelope B F+63*F+73 ∧
--         WordBound F (resetGeneratorState
--           (result s base (initialControlState a) rp rm rs raw shifted)) ∧
--         CandidateReady (resetGeneratorState
--           (result s base (initialControlState a) rp rm rs raw shifted))
--           (a.stacks 141) shifted (selectedHeads s.n s.rows s.low base).length
--           ⟨0,Nat.pow_pos (by decide)⟩ ∧
--         LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
--           (selectedHeads s.n s.rows s.low base) raw ∧
--         List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) raw shifted ∧
--         ∀ prefixSteps intermediate, prefixSteps≤total+1 →
--           Trace (compiled (setupWith loadHead) 0 0) prefixSteps
--             (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) intermediate →
--           ∀ i, (intermediate.stacks i).length≤2000*(F+1)+runEnvelope B F
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.SignedWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Pair` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.selectedHeads` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.lowStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.retainedOutputBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.runEnvelope` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.shiftedWord` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.MatrixRel` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.CacheCorrect` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.relation` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Ready` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.setupWith` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.MasterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.CandidateReady` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.initialControlState` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.resetGeneratorState` (definitions bundle `OAIQ081S152` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.result` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.columnLength` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.loadHead` (definitions bundle `OAIQ081S191` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.setup_rel_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.setup_masterFrame` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleLoader.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.setup_native_run)

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

theorem setup_native_run (s : Native.Inputs) (source : Data) (ha : Native.Ready s source)
    (B : ℕ) (hB : WordBound B source) (hrows : s.rows.length=s.n+s.N)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s source ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (base F L : ℕ) (hbase : a.stacks 649=unary base) (hpositive : 0 < s.r)
    (hf : WordBound F a) (hW : (a.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F) :
    ∃ rp rm rs raw shifted total,
      Eval (setupWith loadHead) total a
        (resetGeneratorState (result s base (initialControlState a) rp rm rs raw shifted)) ∧
      total+1 ≤ runEnvelope B F+63*F+73 ∧
      WordBound F (resetGeneratorState
        (result s base (initialControlState a) rp rm rs raw shifted)) ∧
      CandidateReady (resetGeneratorState
        (result s base (initialControlState a) rp rm rs raw shifted))
        (a.stacks 141) shifted (selectedHeads s.n s.rows s.low base).length
        ⟨0,Nat.pow_pos (by decide)⟩ ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low base) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total+1 →
        Trace (compiled (setupWith loadHead) 0 0) prefixSteps
          (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length≤2000*(F+1)+runEnvelope B F := by
  sorry

end Storage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

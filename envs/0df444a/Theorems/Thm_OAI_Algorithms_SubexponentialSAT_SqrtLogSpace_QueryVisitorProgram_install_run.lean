-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorProgram_install_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.install_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:38:58.810408+00:00
-- url     : https://prove2.me/theorems/4e7555cd-9692-4f51-b83f-5fb214c8da8c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.install_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.install_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorCorrect.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorCorrect.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram`, with `open OAI BitProgram StructuredCalls`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram`, `open QueryTupleState QueryTupleVisitor SignatureTupleProgram SubexpSetupStorage`):
--
--   ```lean
--   theorem install_run {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
--       {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
--       {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
--       {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
--       (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
--       (hv : DenseWord q 852 tupleValue a) (ha : WordBound B a)
--       (htmp : a.stacks 841=[])
--       (hh : (a.stacks 838).length=HighIncidenceProgram.Restriction.highCount (a.stacks 670))
--       (hmask : (a.stacks 670).length=(a.stacks 869).length) :
--       ∃ steps rf, Eval installRepresentative steps a (installedRepresentative a rf) ∧
--         QueryReady q node H high E U P (installedRepresentative a rf) ∧
--         PairAccumulatorMeaning q pairValue (installedRepresentative a rf) ∧
--         DenseWord q 852 tupleValue (installedRepresentative a rf) ∧
--         QueryMasterFrame a (installedRepresentative a rf) ∧
--         WordBound B (installedRepresentative a rf) ∧
--         (installedRepresentative a rf).stacks 869=
--           LeafAssignmentMergeProgram.merge
--             (HighIncidenceProgram.Restriction.zeroMerge (a.stacks 670) (a.stacks 838))
--             (a.stacks 670) (a.stacks 869) ∧
--         (∀ i : Fin 40,16 ≤ i.val → (installedRepresentative a rf).regs i=a.regs i) ∧
--         steps≤90*B+89 ∧
--         QueryExecution.PrefixBound installRepresentative steps a (986*B+89)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.zeroMerge` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.merge` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.installRepresentative` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.PrefixBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.DenseWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.PairAccumulatorMeaning` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryMasterFrame` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.Data` (definitions bundle `OAIQ081S179` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryReady` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.installedRepresentative` (definitions bundle `OAIQ081S185` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_head` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorCorrect.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.install_run)

import Mathlib
import Definitions.Def_OAIQ081S185

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
open OAI BitProgram StructuredCalls

open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SubexpSetupStorage

theorem install_run {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
    {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (hv : DenseWord q 852 tupleValue a) (ha : WordBound B a)
    (htmp : a.stacks 841=[])
    (hh : (a.stacks 838).length=HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hmask : (a.stacks 670).length=(a.stacks 869).length) :
    ∃ steps rf, Eval installRepresentative steps a (installedRepresentative a rf) ∧
      QueryReady q node H high E U P (installedRepresentative a rf) ∧
      PairAccumulatorMeaning q pairValue (installedRepresentative a rf) ∧
      DenseWord q 852 tupleValue (installedRepresentative a rf) ∧
      QueryMasterFrame a (installedRepresentative a rf) ∧
      WordBound B (installedRepresentative a rf) ∧
      (installedRepresentative a rf).stacks 869=
        LeafAssignmentMergeProgram.merge
          (HighIncidenceProgram.Restriction.zeroMerge (a.stacks 670) (a.stacks 838))
          (a.stacks 670) (a.stacks 869) ∧
      (∀ i : Fin 40,16 ≤ i.val → (installedRepresentative a rf).regs i=a.regs i) ∧
      steps≤90*B+89 ∧
      QueryExecution.PrefixBound installRepresentative steps a (986*B+89) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
end

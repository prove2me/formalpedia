-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary_entry_of_query
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.entry_of_query
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:27:28.821722+00:00
-- url     : https://prove2.me/theorems/fa1e7a0e-91ed-429b-abac-83be683936ff
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.entry_of_query: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.entry_of_query` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentBoundary.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentBoundary.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary`, with `open OAI BitProgram StructuredCalls SubexpSetupStorage`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native`, `open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics`, `open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing`, `open FactorAssignmentProgram`):
--
--   ```lean
--   theorem entry_of_query {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
--       {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
--       {a : FactorAssignmentProgram.Data}
--       (h : QueryTupleState.QueryReady q node H high E U M a)
--       (ha : WordBound P a) (hchoices : (a.stacks 145).length = n)
--       (hlow : ∀ i : Fin 56, a.stacks (i.castAdd 840) = [])
--       (hcache : 4*M+6 ≤ P)
--       (hseed : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ P)
--       (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
--         (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S)
--       (hradius : q.p.R+1 ≤ Q) : Entry q P M S a
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop.byteBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.specializedPayloadBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalRecordBound` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.Entry` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryReady` (definitions bundle `OAIQ081S185` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.accepted_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentBoundary.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.entry_of_query)

import Mathlib
import Definitions.Def_OAIQ081S185

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem entry_of_query {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {a : FactorAssignmentProgram.Data}
    (h : QueryTupleState.QueryReady q node H high E U M a)
    (ha : WordBound P a) (hchoices : (a.stacks 145).length = n)
    (hlow : ∀ i : Fin 56, a.stacks (i.castAdd 840) = [])
    (hcache : 4*M+6 ≤ P)
    (hseed : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ P)
    (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
      (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S)
    (hradius : q.p.R+1 ≤ Q) : Entry q P M S a := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
end

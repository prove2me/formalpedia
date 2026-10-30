-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorHead_shifted_source_typed
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.shifted_source_typed
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:59:44.343535+00:00
-- url     : https://prove2.me/theorems/dd1711a0-e854-4282-88a1-4b5969953f16
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.shifted_source_typed: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.shifted_source_typed` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorHead.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorHead.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead`, with `open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram`, `open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadIdentifierProgram`, `open BucketTupleProgram.Concrete QueryTupleState SubexpSetupStorage`, `open scoped BigOperators`):
--
--   ```lean
--   theorem shifted_source_typed (s : LeafHeadSetupProgram.Native.Inputs) {d : ℕ}
--       (q : Factor.Spec s.r s.Q s.n d) (owner : Fin q.ps.length → Fin s.n)
--       (nativeOwner : Fin s.D → Fin s.n) (hD : q.ps.length=s.D)
--       (howner : ∀ i : Fin s.plans.length,
--         (s.plans.get i).1=(nativeOwner (Fin.cast s.plans_length i)).val)
--       (hliteral : ∀ j v,
--         LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R s.node j v=
--         LayoutProducedMatrix.literalNat s.packing nativeOwner s.height.length s.R s.node j v)
--       (W : List Bool) (hW : BinaryArithmetic.toNat W=s.offset) (z : ℕ)
--       (raw : List (List LayoutMatrixProgram.Pair)) (rows : List (List (List Bool)))
--       (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
--         (LeafHeadSetupProgram.selectedHeads s.n s.rows s.low z) raw)
--       (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw rows) :
--       ∃ c : Fin q.ps.length → Fin (count (predicate s.rows s.low z) s.n) → List Bool,
--         rows=List.ofFn (fun j => List.ofFn (c j)) ∧
--         ∀ j i,(BinaryArithmetic.toNat (c j i) : ℤ)=(BinaryArithmetic.toNat W : ℤ)+
--           LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R s.node
--             j.val ((chosenIds (predicate s.rows s.low z) s.n).get i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.SignedWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.chosenIds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.predicate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Pair` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.selectedHeads` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.shiftedWord` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.count` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalNat` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.MatrixRel` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.offset` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.relation` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.columnLength` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.evaluateHead_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorHead.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.shifted_source_typed)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S168
import Definitions.Def_OAIQ081S169

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadIdentifierProgram
open BucketTupleProgram.Concrete QueryTupleState SubexpSetupStorage
open scoped BigOperators
noncomputable section

theorem shifted_source_typed (s : LeafHeadSetupProgram.Native.Inputs) {d : ℕ}
    (q : Factor.Spec s.r s.Q s.n d) (owner : Fin q.ps.length → Fin s.n)
    (nativeOwner : Fin s.D → Fin s.n) (hD : q.ps.length=s.D)
    (howner : ∀ i : Fin s.plans.length,
      (s.plans.get i).1=(nativeOwner (Fin.cast s.plans_length i)).val)
    (hliteral : ∀ j v,
      LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R s.node j v=
      LayoutProducedMatrix.literalNat s.packing nativeOwner s.height.length s.R s.node j v)
    (W : List Bool) (hW : BinaryArithmetic.toNat W=s.offset) (z : ℕ)
    (raw : List (List LayoutMatrixProgram.Pair)) (rows : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (LeafHeadSetupProgram.selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw rows) :
    ∃ c : Fin q.ps.length → Fin (count (predicate s.rows s.low z) s.n) → List Bool,
      rows=List.ofFn (fun j => List.ofFn (c j)) ∧
      ∀ j i,(BinaryArithmetic.toNat (c j i) : ℤ)=(BinaryArithmetic.toNat W : ℤ)+
        LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R s.node
          j.val ((chosenIds (predicate s.rows s.low z) s.n).get i) := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
end

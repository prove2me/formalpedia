-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumCorrect_gate_source_iff
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.gate_source_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:56:37.406614+00:00
-- url     : https://prove2.me/theorems/cfab5e66-db94-4fd7-840a-9266aec8b1b3
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.gate_source_iff: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.gate_source_iff` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumCorrect.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumCorrect.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect`, with `open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram`, `open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram`, `open scoped BigOperators`, `open HeadIdentifierProgram`, `open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete`):
--
--   ```lean
--   theorem gate_source_iff {r Q d n : ℕ} (p : SourceBank.Parameters r Q d)
--       (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
--       (owner : Fin ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
--       (H E : Finset (Fin n)) (node : Fin Q) (g : Fin r) (pick : ℕ → Bool)
--       (hs : ∀ v : Fin n, v.val ∈ chosenIds pick n ↔ ∃ _ : v ∉ H, head node v = g)
--       (W : List Bool) (c : Fin ps.length → Fin (count pick n) → List Bool)
--       (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
--         (BinaryArithmetic.toNat W : ℤ) +
--           LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node j.val
--             ((chosenIds pick n).get i))
--       (candidate representative : Moments.Head
--         (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool)
--       (a : HeadSumProgram.Data) (hW : a.stacks 864 = W)
--       (hbits : a.stacks 859 = List.ofFn (freeAssignmentEquiv H
--         (fun v => head node v.val) g (chosenIds pick n)
--         (chosenIds_bound pick n) (chosenIds_nodup pick n) hs candidate))
--       (hkey : a.stacks 866 = BucketProgram.signatureValue W
--         (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
--           (chosenIds_bound pick n) (chosenIds_nodup pick n) hs representative))
--         (List.ofFn (fun j => List.ofFn (c j))))
--       (hE : a.stacks 867 = HighIncidenceProgram.Restriction.selected true
--         (List.ofFn (fun v : Fin n => pick v.val)) (LeafWeightProgram.supportBits ⟨E⟩))
--       (hH : a.stacks 868 = List.replicate (count pick n) true) :
--       gateValue a (List.ofFn (fun j => List.ofFn (c j))) = true ↔
--         HeadSourceLocality.freeLabel p ps P owner head H node g candidate =
--           HeadSourceLocality.freeLabel p ps P owner head H node g representative ∧
--         ∀ v : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g,
--           v.val.val ∈ E → candidate v = true
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.chosenIds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.Head` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Support` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.Free` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signatureValue` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete.freeAssignmentEquiv` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.chosenIds_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.chosenIds_nodup` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.count` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalNat` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.supportBits` (definitions bundle `OAIQ081S077` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.gateValue` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.freeLabel` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumCorrect.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.gate_source_iff)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S172

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect

open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram
open scoped BigOperators

open HeadIdentifierProgram

open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

theorem gate_source_iff {r Q d n : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (H E : Finset (Fin n)) (node : Fin Q) (g : Fin r) (pick : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds pick n ↔ ∃ _ : v ∉ H, head node v = g)
    (W : List Bool) (c : Fin ps.length → Fin (count pick n) → List Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) +
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node j.val
          ((chosenIds pick n).get i))
    (candidate representative : Moments.Head
      (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool)
    (a : HeadSumProgram.Data) (hW : a.stacks 864 = W)
    (hbits : a.stacks 859 = List.ofFn (freeAssignmentEquiv H
      (fun v => head node v.val) g (chosenIds pick n)
      (chosenIds_bound pick n) (chosenIds_nodup pick n) hs candidate))
    (hkey : a.stacks 866 = BucketProgram.signatureValue W
      (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
        (chosenIds_bound pick n) (chosenIds_nodup pick n) hs representative))
      (List.ofFn (fun j => List.ofFn (c j))))
    (hE : a.stacks 867 = HighIncidenceProgram.Restriction.selected true
      (List.ofFn (fun v : Fin n => pick v.val)) (LeafWeightProgram.supportBits ⟨E⟩))
    (hH : a.stacks 868 = List.replicate (count pick n) true) :
    gateValue a (List.ofFn (fun j => List.ofFn (c j))) = true ↔
      HeadSourceLocality.freeLabel p ps P owner head H node g candidate =
        HeadSourceLocality.freeLabel p ps P owner head H node g representative ∧
      ∀ v : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g,
        v.val.val ∈ E → candidate v = true := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect
end

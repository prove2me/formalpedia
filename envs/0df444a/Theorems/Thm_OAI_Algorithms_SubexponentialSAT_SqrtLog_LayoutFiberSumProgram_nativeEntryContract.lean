-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutFiberSumProgram_nativeEntryContract
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeEntryContract
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:02:14.345376+00:00
-- url     : https://prove2.me/theorems/0b22d4fd-17f0-4c06-830b-e25f0c266347
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeEntryContract: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeEntryContract` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutFiberSumProgramContract.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutFiberSumProgramContract.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes`, `open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram`):
--
--   ```lean
--   theorem nativeEntryContract {r Q D : ℕ}
--       (P : PackingData (Fin D) (UniversalType r Q 1))
--       (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
--       (aWord : List Bool) (R : ℕ) (t : Fin Q)
--       (base : Fin 288 → List Bool) (ps : List (ℕ × ℕ))
--       (Valid : ℕ → ℕ → Prop) (S U H Tout Bout : ℕ)
--       (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
--       (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
--       (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
--       (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
--       (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
--       (hc : LayoutProgram.EntryBank.CacheWords (r:=r) (matrixBase base 0)
--         (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t)
--       (hready : ∀ j v, Valid j v → Ready (matrixBase base j))
--       (hmeta : base (LayoutMatrixProgram.bankPort 200)=
--         SelectorProgram.rawRecords (LayoutProgram.EntryBank.metadataRecords P))
--       (hsource : base (LayoutMatrixProgram.bankPort 201)=LayoutOwnerFiberProgram.stream ps)
--       (hsize : ∀ i : Fin 256, i.val < 212 → (base (LayoutMatrixProgram.bankPort i)).length ≤ S)
--       (hps : ps.length=D) (hDS : D ≤ S)
--       (hvalid : ∀ j v, Valid j v → j < D)
--       (hmetadata : ∀ v, LayoutProgram.EntryBank.MetadataBound
--         (PackingMetadata.value P CollisionProgram.encodeType v) S)
--       (hlookup : ∀ row col : Fin D, LayoutProgram.EntryBank.lookupBudget P row col ≤ U)
--       (htime : ∀ j v, Valid j v →
--         budget (nativeTime r Q R width power aWord S U) (nativeLength R width power)
--           ps.length v ps ≤ Tout)
--       (hlength : ∀ j v, Valid j v →
--         (LayoutOwnerFiberProgram.fiberIndices v 0 ps).length*(nativeLength R width power+2) ≤ Bout)
--       (hmass : ∀ j v, Valid j v →
--         (LayoutOwnerFiberProgram.fiberIndices v 0 ps).length*LayoutProgram.constraintMassBound Q R ≤ H) :
--       LayoutMatrixProgram.EntryContract (command LayoutProgram.EntryBank.command) base Valid
--         (BucketProgram.ProducedRank.FiberRel ps
--           (BucketProgram.ProducedRank.entryNat P aWord.length R t) H) Tout Bout
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.fiberIndices`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.H` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.bankPort` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.constraintMassBound` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram.encodeType` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.FiberRel` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.rawRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata.value` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.entryNat` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.wordTotal` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.stream` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.MetadataBound` (definitions bundle `OAIQ081S073` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.lookupBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.metadataRecords` (definitions bundle `OAIQ081S089` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.Ready` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.matrixBase` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.EntryContract` (definitions bundle `OAIQ081S122` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeLength` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeTime` (definitions bundle `OAIQ081S142` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.CacheWords` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.unsignedSaved` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad_load_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.initial_contract` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutFiberSumProgramContract.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeEntryContract)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

theorem nativeEntryContract {r Q D : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (R : ℕ) (t : Fin Q)
    (base : Fin 288 → List Bool) (ps : List (ℕ × ℕ))
    (Valid : ℕ → ℕ → Prop) (S U H Tout Bout : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
    (hc : LayoutProgram.EntryBank.CacheWords (r:=r) (matrixBase base 0)
      (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t)
    (hready : ∀ j v, Valid j v → Ready (matrixBase base j))
    (hmeta : base (LayoutMatrixProgram.bankPort 200)=
      SelectorProgram.rawRecords (LayoutProgram.EntryBank.metadataRecords P))
    (hsource : base (LayoutMatrixProgram.bankPort 201)=LayoutOwnerFiberProgram.stream ps)
    (hsize : ∀ i : Fin 256, i.val < 212 → (base (LayoutMatrixProgram.bankPort i)).length ≤ S)
    (hps : ps.length=D) (hDS : D ≤ S)
    (hvalid : ∀ j v, Valid j v → j < D)
    (hmetadata : ∀ v, LayoutProgram.EntryBank.MetadataBound
      (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hlookup : ∀ row col : Fin D, LayoutProgram.EntryBank.lookupBudget P row col ≤ U)
    (htime : ∀ j v, Valid j v →
      budget (nativeTime r Q R width power aWord S U) (nativeLength R width power)
        ps.length v ps ≤ Tout)
    (hlength : ∀ j v, Valid j v →
      (LayoutOwnerFiberProgram.fiberIndices v 0 ps).length*(nativeLength R width power+2) ≤ Bout)
    (hmass : ∀ j v, Valid j v →
      (LayoutOwnerFiberProgram.fiberIndices v 0 ps).length*LayoutProgram.constraintMassBound Q R ≤ H) :
    LayoutMatrixProgram.EntryContract (command LayoutProgram.EntryBank.command) base Valid
      (BucketProgram.ProducedRank.FiberRel ps
        (BucketProgram.ProducedRank.entryNat P aWord.length R t) H) Tout Bout := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

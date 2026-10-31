-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutFiberSumProgram_entryAt
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.entryAt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:02:54.794747+00:00
-- url     : https://prove2.me/theorems/2d598c06-ef2c-48cb-908d-a002e87ae44e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.entryAt: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.entryAt` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutFiberSumProgramNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutFiberSumProgramNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes`, `open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram`):
--
--   ```lean
--   theorem entryAt {r Q D : ℕ} (P : PackingData (Fin D) (UniversalType r Q 1))
--       (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
--       (aWord : List Bool) (R : ℕ) (t : Fin Q) (row col : Fin D)
--       (base : Data) (S U : ℕ)
--       (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
--       (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
--       (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
--       (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
--       (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
--       (hc : LayoutProgram.EntryBank.CacheWords (r:=r) base
--         (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t)
--       (hwork : ∀ i : Fin 256, i.val < 200 → base.stacks i=[])
--       (hmeta : base.stacks 200=SelectorProgram.rawRecords (LayoutProgram.EntryBank.metadataRecords P))
--       (hrow : base.stacks 252=List.replicate row.val true)
--       (hsize : ∀ i : Fin 256, i.val < 212 → (base.stacks i).length ≤ S)
--       (hrs : row.val ≤ S) (hcs : col.val ≤ S)
--       (hmetadata : ∀ v, LayoutProgram.EntryBank.MetadataBound
--         (PackingMetadata.value P CollisionProgram.encodeType v) S)
--       (hlookup : LayoutProgram.EntryBank.lookupBudget P row col ≤ U) :
--       EntryAt LayoutProgram.EntryBank.command base (incidenceValue P aWord.length R t row)
--         (nativeTime r Q R width power aWord S U) (nativeLength R width power)
--         (LayoutProgram.constraintMassBound Q R) col.val
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.H` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.constraintMassBound` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue` and `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram.encodeType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.rawRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata.value` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.wordTotal` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.incidenceValue` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.MetadataBound` (definitions bundle `OAIQ081S073` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.Data` (definitions bundle `OAIQ081S087` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.lookupBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.metadataRecords` (definitions bundle `OAIQ081S089` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.EntryAt` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeLength` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeTime` (definitions bundle `OAIQ081S142` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.CacheWords` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.unsignedSaved` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeEntryContract` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutFiberSumProgramNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.entryAt)

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

theorem entryAt {r Q D : ℕ} (P : PackingData (Fin D) (UniversalType r Q 1))
    (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (R : ℕ) (t : Fin Q) (row col : Fin D)
    (base : Data) (S U : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
    (hc : LayoutProgram.EntryBank.CacheWords (r:=r) base
      (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t)
    (hwork : ∀ i : Fin 256, i.val < 200 → base.stacks i=[])
    (hmeta : base.stacks 200=SelectorProgram.rawRecords (LayoutProgram.EntryBank.metadataRecords P))
    (hrow : base.stacks 252=List.replicate row.val true)
    (hsize : ∀ i : Fin 256, i.val < 212 → (base.stacks i).length ≤ S)
    (hrs : row.val ≤ S) (hcs : col.val ≤ S)
    (hmetadata : ∀ v, LayoutProgram.EntryBank.MetadataBound
      (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hlookup : LayoutProgram.EntryBank.lookupBudget P row col ≤ U) :
    EntryAt LayoutProgram.EntryBank.command base (incidenceValue P aWord.length R t row)
      (nativeTime r Q R width power aWord S U) (nativeLength R width power)
      (LayoutProgram.constraintMassBound Q R) col.val := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

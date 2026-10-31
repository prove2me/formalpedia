-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_EntryBank_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:03:20.294429+00:00
-- url     : https://prove2.me/theorems/a46d70c7-99f6-4a5f-ba25-600ff320de6b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes`, `open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram`):
--
--   ```lean
--   theorem command_eval (P : PackingData (Fin D) (UniversalType r Q 1))
--       (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
--       (aWord : List Bool) (R : ℕ) (t : Fin Q) (row col : Fin D)
--       (a : Data) (S K L : ℕ)
--       (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
--       (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
--       (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
--       (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
--       (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
--       (hc : CacheWords (r:=r) a (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t)
--       (hready : BaseReady a)
--       (hmeta : a.stacks 200=SelectorProgram.rawRecords (metadataRecords P))
--       (hrow : a.stacks 252=List.replicate row.val true)
--       (hcol : a.stacks 253=List.replicate col.val true)
--       (hsize : ∀ j : Fin 256,j.val < 212 → (a.stacks j).length ≤ S)
--       (hrs : row.val ≤ S) (hcs : col.val ≤ S)
--       (hmetadata : ∀ v, MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
--       (hK : ∀ u y : UniversalType r Q 1, IntegerEntry.budget aWord.length R width.length (pairLength power) power.1.length t u y ≤ K)
--       (hL : ∀ u y : UniversalType r Q 1, IntegerEntry.lengthBound R width.length (pairLength power) u y+power.1.length+1 ≤ L)
--       (hL1 : 1 ≤ L) :
--       ∃ n ≤ lookupBudget P row col+K+550*S+450*L+1200, ∃ rf result,
--         Eval command n a (finish a rf result) ∧
--         pairValue result=localEntry P aWord.length R t row col ∧
--         LayoutProgramScalar.wordTotal result ≤ constraintMassBound Q R ∧ pairLength result ≤ L
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.H` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.constraintMassBound` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.localEntry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue` and `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram.encodeType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.rawRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata.value` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.wordTotal` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.MetadataBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.lengthBound` (definitions bundle `OAIQ081S073` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.lookupBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.metadataRecords` (definitions bundle `OAIQ081S089` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.Data` (definitions bundle `OAIQ081S142` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.BaseReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.CacheWords` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.finish` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.unsignedSaved` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.entryAt` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

variable {r Q D : ℕ}

theorem command_eval (P : PackingData (Fin D) (UniversalType r Q 1))
    (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (R : ℕ) (t : Fin Q) (row col : Fin D)
    (a : Data) (S K L : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
    (hc : CacheWords (r:=r) a (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t)
    (hready : BaseReady a)
    (hmeta : a.stacks 200=SelectorProgram.rawRecords (metadataRecords P))
    (hrow : a.stacks 252=List.replicate row.val true)
    (hcol : a.stacks 253=List.replicate col.val true)
    (hsize : ∀ j : Fin 256,j.val < 212 → (a.stacks j).length ≤ S)
    (hrs : row.val ≤ S) (hcs : col.val ≤ S)
    (hmetadata : ∀ v, MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hK : ∀ u y : UniversalType r Q 1, IntegerEntry.budget aWord.length R width.length (pairLength power) power.1.length t u y ≤ K)
    (hL : ∀ u y : UniversalType r Q 1, IntegerEntry.lengthBound R width.length (pairLength power) u y+power.1.length+1 ≤ L)
    (hL1 : 1 ≤ L) :
    ∃ n ≤ lookupBudget P row col+K+550*S+450*L+1200, ∃ rf result,
      Eval command n a (finish a rf result) ∧
      pairValue result=localEntry P aWord.length R t row col ∧
      LayoutProgramScalar.wordTotal result ≤ constraintMassBound Q R ∧ pairLength result ≤ L := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

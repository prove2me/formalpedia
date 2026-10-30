-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:41:12.268459+00:00
-- url     : https://prove2.me/theorems/3af14b8b-07a9-457e-ac16-9a9bfad53199
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes`, `open SubexponentialSAT.Subexp.ConstructivePacking IntegerRingLiftProgram RowSelectionProgram`):
--
--   ```lean
--   theorem command_eval (p : Parameters r Q d)
--       (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : Fin D)
--       (a : Data) (ha : Ready p a) (S : ℕ)
--       (hclean : ∀ j∈cleanupPorts,a.stacks j=[])
--       (hmeta : a.stacks 306=SelectorProgram.rawRecords (metadataRecords P))
--       (hrow : a.stacks 304=List.replicate row.val true)
--       (hcol : a.stacks 305=List.replicate col.val true)
--       (hsize : ∀ j,(a.stacks j).length ≤ S)
--       (hmetadata : ∀ v,MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
--       (hQ : Q ≤ S) (hR : p.R ≤ S) (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
--       ∃ n ≤ lookupBudget P row col+uniformBudget p S+200*S+300,
--         ∃ b : Data, ∃ bytes : List Bool, Eval command n a b ∧
--           b.stacks=Function.update a.stacks 287 bytes ∧
--           SourceWitness.Generated p.ops p.R (UniversalRowSourceBound.sourceLengthBound S)
--             (packedValue P p.rows row col) bytes
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.cleanupPorts` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.sourceLengthBound` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` and `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram.encodeType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.rawRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata.value` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.packedValue` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.MetadataBound` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.metadataRecords` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.lookupBudget` (definitions bundle `OAIQ081S107` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.Generated` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Data` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.uniformBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.rows` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Ready` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command` (definitions bundle `OAIQ081S186` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.native_relSourceSpec` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command_eval)

import Mathlib
import Definitions.Def_OAIQ081S186

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking IntegerRingLiftProgram RowSelectionProgram

variable {r Q d D : ℕ}

theorem command_eval (p : Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : Fin D)
    (a : Data) (ha : Ready p a) (S : ℕ)
    (hclean : ∀ j∈cleanupPorts,a.stacks j=[])
    (hmeta : a.stacks 306=SelectorProgram.rawRecords (metadataRecords P))
    (hrow : a.stacks 304=List.replicate row.val true)
    (hcol : a.stacks 305=List.replicate col.val true)
    (hsize : ∀ j,(a.stacks j).length ≤ S)
    (hmetadata : ∀ v,MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hQ : Q ≤ S) (hR : p.R ≤ S) (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
    ∃ n ≤ lookupBudget P row col+uniformBudget p S+200*S+300,
      ∃ b : Data, ∃ bytes : List Bool, Eval command n a b ∧
        b.stacks=Function.update a.stacks 287 bytes ∧
        SourceWitness.Generated p.ops p.R (UniversalRowSourceBound.sourceLengthBound S)
          (packedValue P p.rows row col) bytes := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

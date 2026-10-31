-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_native_relSourceSpec
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.native_relSourceSpec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:47:43.431852+00:00
-- url     : https://prove2.me/theorems/4cca75ac-50af-4428-bb6b-572a44b93d74
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.native_relSourceSpec: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.native_relSourceSpec` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramPacked.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramPacked.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp`, `open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes`, `open LayoutProgram`):
--
--   ```lean
--   theorem native_relSourceSpec {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
--       (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D)
--       (base : Store) (I S : ℕ) (hID : I < D) (hIS : I ≤ S)
--       (hready : SourceBank.Ready p (⟨fun _ => false,base ∘ sourcePorts⟩ : SourceBank.Data))
--       (hclean : ∀ j∈SourceBank.cleanupPorts, base (sourcePorts j)=[])
--       (hmeta : base 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
--       (hrow : base 304=List.replicate row.val true)
--       (hsize : ∀ j : Fin 320, (base (sourcePorts j)).length ≤ S)
--       (hmetadata : ∀ v,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
--       (hQ : Q ≤ S) (hR : p.R ≤ S) (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
--       RelSourceSpec packedSource base
--         (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (SubexpLiftRing.baseWidth 3 p.t) d)) =>
--           SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
--         (TypedSourceRel DensePolynomialProgram.encode (PolynomialExecutorProgram.meaning p.ops)
--           (packedSourceValue p P row) (Subexp.UniversalRowSourceBound.sourceLengthBound S))
--         I (nativeSourceBudget p S) (Subexp.UniversalRowSourceBound.sourceLengthBound S)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.compile` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.cleanupPorts` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourcePorts` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.sourceLengthBound` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` and `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram.encodeType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.rawRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl.serializeCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.TypedSourceRel` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata.value` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.MetadataBound` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.metadataRecords` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.encode` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RelSourceSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.meaning` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeSourceBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.packedSourceValue` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Ready` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.packedSource` (definitions bundle `OAIQ081S186` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.staged_native_row_relSourceSpec` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramPacked.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.native_relSourceSpec)

import Mathlib
import Definitions.Def_OAIQ081S186

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes
open LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem native_relSourceSpec {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D)
    (base : Store) (I S : ℕ) (hID : I < D) (hIS : I ≤ S)
    (hready : SourceBank.Ready p (⟨fun _ => false,base ∘ sourcePorts⟩ : SourceBank.Data))
    (hclean : ∀ j∈SourceBank.cleanupPorts, base (sourcePorts j)=[])
    (hmeta : base 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
    (hrow : base 304=List.replicate row.val true)
    (hsize : ∀ j : Fin 320, (base (sourcePorts j)).length ≤ S)
    (hmetadata : ∀ v,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hQ : Q ≤ S) (hR : p.R ≤ S) (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
    RelSourceSpec packedSource base
      (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (SubexpLiftRing.baseWidth 3 p.t) d)) =>
        SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
      (TypedSourceRel DensePolynomialProgram.encode (PolynomialExecutorProgram.meaning p.ops)
        (packedSourceValue p P row) (Subexp.UniversalRowSourceBound.sourceLengthBound S))
      I (nativeSourceBudget p S) (Subexp.UniversalRowSourceBound.sourceLengthBound S) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

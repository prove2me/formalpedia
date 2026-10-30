-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRows_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:45:51.989734+00:00
-- url     : https://prove2.me/theorems/11f2054f-233f-462b-93e5-ec3cc6c66528
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp`, `open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram`, `open SubexponentialSAT.SubexpLiftRing`):
--
--   ```lean
--   theorem sourceRows_run {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
--       (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
--       (s : Store) (v N f S : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
--       (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts)
--         (p.R+1) (d*baseWidth 3 p.t))
--       (hv : s 233=LayoutSourcePlanLookup.unary v)
--       (hN : s 212=LayoutSourcePlanLookup.unary N)
--       (hf : s 216=LayoutSourcePlanLookup.unary f)
--       (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
--       (hlookup : LayoutSourcePlanLookup.Native.Clean
--         (⟨fun _ => false,initializeFinish s (p.R+1) (d*baseWidth 3 p.t)⟩ : Data))
--       (hclean : RowsClean (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f))
--       (hwork : RowWorkClean (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f))
--       (howner : ∀ i : Fin 11, (2 : ℕ) ≤ i.val →
--         (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (ownerStacks i)=[])
--       (H : DensePolynomialProgram.PairSpec.BaseReady 3 p.t p.modulus p.cache
--         (HornerProgram.modelTable p.t p.model p.modulus p.cache) (s ∘ executorPorts) width frame)
--       (E : LayoutSourceRowsProgramReadiness.Empty s)
--       (hready : SourceBank.Ready p (⟨fun _ => false,
--         clearedSourceStore (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) ∘ sourcePorts⟩ : SourceBank.Data))
--       (hsourceClean : ∀ j∈SourceBank.cleanupPorts,
--         (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (sourcePorts j)=[])
--       (hmeta : s 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
--       (hsize : ∀ j : Fin 320,
--         ((preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (sourcePorts j)).length ≤ S)
--       (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
--       (hD : ps.length ≤ S) (hQ : Q ≤ S) (hR : p.R ≤ S)
--       (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S)
--       (regs : Fin 16 → Bool) :
--       ∃ rows n rf,
--         RowProperty DensePolynomialProgram.encode
--           (fun j out => PolynomialExecutorProgram.meaning p.ops out=
--             sourceRowFamily ps N f v (totalPackedSource p P) j)
--           ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows ∧ rows.length=N ∧
--         n ≤ nativeRowsBudget p s v N f S ps ∧
--         Eval sourceRows n (⟨regs,s⟩ : Data)
--           (⟨rf,Function.update (initializeFinish s (p.R+1) (d*baseWidth 3 p.t)) 205
--             (Encoding.encodeList DensePolynomialProgram.encode rows)⟩ : Data)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.cleanupPorts` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowProperty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowWorkClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowsClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.clearedSourceStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.executorPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.initializationPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.initializeFinish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.ownerStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.preparedSourceStore` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourcePorts` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` and `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram.encodeType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.rawRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowFamily` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata.value` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize.Ready` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness.Empty` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.stream` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.MetadataBound` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.metadataRecords` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.Clean` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.encode` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.modelTable` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.meaning` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.totalPackedSource` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Ready` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows` (definitions bundle `OAIQ081S186` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_run)

import Mathlib
import Definitions.Def_SubexponentialSAT
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
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open SubexponentialSAT.SubexpLiftRing

theorem sourceRows_run {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (s : Store) (v N f S : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts)
      (p.R+1) (d*baseWidth 3 p.t))
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s (p.R+1) (d*baseWidth 3 p.t)⟩ : Data))
    (hclean : RowsClean (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f))
    (hwork : RowWorkClean (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f))
    (howner : ∀ i : Fin 11, (2 : ℕ) ≤ i.val →
      (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (ownerStacks i)=[])
    (H : DensePolynomialProgram.PairSpec.BaseReady 3 p.t p.modulus p.cache
      (HornerProgram.modelTable p.t p.model p.modulus p.cache) (s ∘ executorPorts) width frame)
    (E : LayoutSourceRowsProgramReadiness.Empty s)
    (hready : SourceBank.Ready p (⟨fun _ => false,
      clearedSourceStore (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) ∘ sourcePorts⟩ : SourceBank.Data))
    (hsourceClean : ∀ j∈SourceBank.cleanupPorts,
      (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (sourcePorts j)=[])
    (hmeta : s 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
    (hsize : ∀ j : Fin 320,
      ((preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (sourcePorts j)).length ≤ S)
    (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
    (hD : ps.length ≤ S) (hQ : Q ≤ S) (hR : p.R ≤ S)
    (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S)
    (regs : Fin 16 → Bool) :
    ∃ rows n rf,
      RowProperty DensePolynomialProgram.encode
        (fun j out => PolynomialExecutorProgram.meaning p.ops out=
          sourceRowFamily ps N f v (totalPackedSource p P) j)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows ∧ rows.length=N ∧
      n ≤ nativeRowsBudget p s v N f S ps ∧
      Eval sourceRows n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update (initializeFinish s (p.R+1) (d*baseWidth 3 p.t)) 205
          (Encoding.encodeList DensePolynomialProgram.encode rows)⟩ : Data) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

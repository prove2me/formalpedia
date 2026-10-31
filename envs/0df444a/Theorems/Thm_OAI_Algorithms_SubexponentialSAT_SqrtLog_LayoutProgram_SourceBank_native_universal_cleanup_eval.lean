-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_native_universal_cleanup_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_universal_cleanup_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:44:01.496467+00:00
-- url     : https://prove2.me/theorems/8185029d-8b0e-4726-ac0d-bc923c9cb1ee
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_universal_cleanup_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_universal_cleanup_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrameNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrameNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes`, `open IntegerRingLiftProgram`, `open RowSelectionProgram (WordPair pairValue pairLength)`):
--
--   ```lean
--   theorem native_universal_cleanup_eval {r Q d : ℕ}
--       (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
--       (as : List Bool) (R : ℕ) (start : Fin Q) (u y : UniversalType r Q 1)
--       (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
--       (hvalues : Hwords.map BinaryArithmetic.toNat=
--         (List.range R).map (LayoutCoefficientRecurrence.H as.length))
--       (hp : pairValue power=(2:ℤ)^(R-1))
--       (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
--       (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
--       (t : ℕ) (ht : 0 < t) (hd : 0 < d) (model : RingModel.Data d)
--       (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
--       (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
--       (zero one minusOne invDenom : ModelCode t d)
--       (hzero : (RingProgram.modelRing t ht hd model M cache).decode zero=0)
--       (hone : (RingProgram.modelRing t ht hd model M cache).decode one=1)
--       (hminus : (RingProgram.modelRing t ht hd model M cache).decode minusOne= -1)
--       (integerWord : ℤ → ModelCode t d)
--       (hinteger : ∀ z,(RingProgram.modelRing t ht hd model M cache).decode (integerWord z)=
--         (z:model.O t))
--       (a : Data) (htemp : a.stacks 319=[]) (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
--       (ready : CachedReady t model M cache zero one minusOne
--         (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks)
--       (hinv : (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks 252=
--         RingProgram.flat invDenom)
--       (hinput : ∀ i,(projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks
--         (LayoutSourceValuesProgram.Native.numeratorPorts i)=
--         (Numerator.state (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
--           (fun _=>false) start u y [] [] ([],[])).stacks i)
--       (hq : (a.stacks 22).length=Q) (h37 : a.stacks 37=[])
--       (h64 : a.stacks 64=[]) (h65 : a.stacks 65=[]) (h67 : a.stacks 67=[]) (h71 : a.stacks 71=[])
--       (hc : EmitterClean a) (h274 : a.stacks 274=[])
--       (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[]) (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[])
--       (inverse negative : Fin Q → ModelCode t d) (difference : Fin Q → Fin Q → ModelCode t d)
--       (ringWidth rowWidth : List Bool) (hringWidth : ringWidth.length=d*SubexpLiftRing.baseWidth 3 t)
--       (hrowWidth : rowWidth.length=Q*ringWidth.length)
--       (hi : a.stacks 308=(List.ofFn (fun i=>RingProgram.flat (inverse i))).flatten)
--       (hn : a.stacks 309=(List.ofFn (fun i=>RingProgram.flat (negative i))).flatten)
--       (hr : a.stacks 310=(List.ofFn (fun i=>
--         (List.ofFn (fun j=>RingProgram.flat (difference i j))).flatten)).flatten)
--       (hw : a.stacks 311=ringWidth) (hrw : a.stacks 312=rowWidth)
--       (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
--       ∃ codes : Fin Q → ModelCode t d,
--         (∀ node,(RingProgram.modelRing t ht hd model M cache).decode (codes node)=
--           (RingProgram.modelRing t ht hd model M cache).decode
--             (sourceValue (RingProgram.modelRing t ht hd model M cache).program
--               integerWord invDenom as.length R u 0 y node)) ∧
--         ∃ n ≤ Staging.cost 0 1 stageTypesOps a+
--             LayoutSourceValuesProgram.Native.tableBudget as.length R width.length (pairLength power) t d u y+
--             (UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
--               UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13)+
--             finishBound (SourceTyped.tables RingProgram.flat codes inverse negative difference)
--               ringWidth rowWidth (nativePositions u y)
--               (branchState a (fun _=>false) (List.ofFn (fun i=>RingProgram.flat (codes i))).flatten
--                 (nativeIndices u y))
--               (B+Q*(d*SubexpLiftRing.baseWidth 3 t)+(nativeIndices u y).length),
--           ∃ b : Data, Eval (.seq universal cleanup) n a b ∧
--             b.stacks=Function.update (clearedStacks a) 287
--               (UniversalRowProgram.rowCode (a.stacks 313) (a.stacks 314) (a.stacks 313++a.stacks 314)
--                 (UniversalRowDataProgram.row
--                   (SourceTyped.tables RingProgram.flat codes inverse negative difference)
--                   (nativePositions u y)
--                   (if a.stacks 289=a.stacks 292 then a.stacks 314 else a.stacks 313) (a.stacks 47)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.H` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowGather.Word`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.vectorPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.numeratorPorts` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.row`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.stageTypesOps` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.tables` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.wordTotal` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.extractBudget` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceValue` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.nativePositions`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Staging.cost` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Staging.result` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableBudget` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.ModelCode` (definitions bundle `OAIQ081S120` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.cleanup` (definitions bundle `OAIQ081S124` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.nativeIndices` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.CachedReady` (definitions bundle `OAIQ081S140` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.state` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Data` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.unsignedSaved` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.EmitterClean` (definitions bundle `OAIQ081S167` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.branchState` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.clearedStacks` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.rowCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finishBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universal` (definitions bundle `OAIQ081S186` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universal_generated` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrameNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_universal_cleanup_eval)

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

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram
open RowSelectionProgram (WordPair pairValue pairLength)

theorem native_universal_cleanup_eval {r Q d : ℕ}
    (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (as : List Bool) (R : ℕ) (start : Fin Q) (u y : UniversalType r Q 1)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=
      (List.range R).map (LayoutCoefficientRecurrence.H as.length))
    (hp : pairValue power=(2:ℤ)^(R-1))
    (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
    (t : ℕ) (ht : 0 < t) (hd : 0 < d) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd model M cache).decode zero=0)
    (hone : (RingProgram.modelRing t ht hd model M cache).decode one=1)
    (hminus : (RingProgram.modelRing t ht hd model M cache).decode minusOne= -1)
    (integerWord : ℤ → ModelCode t d)
    (hinteger : ∀ z,(RingProgram.modelRing t ht hd model M cache).decode (integerWord z)=
      (z:model.O t))
    (a : Data) (htemp : a.stacks 319=[]) (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
    (ready : CachedReady t model M cache zero one minusOne
      (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks)
    (hinv : (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks 252=
      RingProgram.flat invDenom)
    (hinput : ∀ i,(projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks
      (LayoutSourceValuesProgram.Native.numeratorPorts i)=
      (Numerator.state (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
        (fun _=>false) start u y [] [] ([],[])).stacks i)
    (hq : (a.stacks 22).length=Q) (h37 : a.stacks 37=[])
    (h64 : a.stacks 64=[]) (h65 : a.stacks 65=[]) (h67 : a.stacks 67=[]) (h71 : a.stacks 71=[])
    (hc : EmitterClean a) (h274 : a.stacks 274=[])
    (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[]) (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[])
    (inverse negative : Fin Q → ModelCode t d) (difference : Fin Q → Fin Q → ModelCode t d)
    (ringWidth rowWidth : List Bool) (hringWidth : ringWidth.length=d*SubexpLiftRing.baseWidth 3 t)
    (hrowWidth : rowWidth.length=Q*ringWidth.length)
    (hi : a.stacks 308=(List.ofFn (fun i=>RingProgram.flat (inverse i))).flatten)
    (hn : a.stacks 309=(List.ofFn (fun i=>RingProgram.flat (negative i))).flatten)
    (hr : a.stacks 310=(List.ofFn (fun i=>
      (List.ofFn (fun j=>RingProgram.flat (difference i j))).flatten)).flatten)
    (hw : a.stacks 311=ringWidth) (hrw : a.stacks 312=rowWidth)
    (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∃ codes : Fin Q → ModelCode t d,
      (∀ node,(RingProgram.modelRing t ht hd model M cache).decode (codes node)=
        (RingProgram.modelRing t ht hd model M cache).decode
          (sourceValue (RingProgram.modelRing t ht hd model M cache).program
            integerWord invDenom as.length R u 0 y node)) ∧
      ∃ n ≤ Staging.cost 0 1 stageTypesOps a+
          LayoutSourceValuesProgram.Native.tableBudget as.length R width.length (pairLength power) t d u y+
          (UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
            UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13)+
          finishBound (SourceTyped.tables RingProgram.flat codes inverse negative difference)
            ringWidth rowWidth (nativePositions u y)
            (branchState a (fun _=>false) (List.ofFn (fun i=>RingProgram.flat (codes i))).flatten
              (nativeIndices u y))
            (B+Q*(d*SubexpLiftRing.baseWidth 3 t)+(nativeIndices u y).length),
        ∃ b : Data, Eval (.seq universal cleanup) n a b ∧
          b.stacks=Function.update (clearedStacks a) 287
            (UniversalRowProgram.rowCode (a.stacks 313) (a.stacks 314) (a.stacks 313++a.stacks 314)
              (UniversalRowDataProgram.row
                (SourceTyped.tables RingProgram.flat codes inverse negative difference)
                (nativePositions u y)
                (if a.stacks 289=a.stacks 292 then a.stacks 314 else a.stacks 313) (a.stacks 47))) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

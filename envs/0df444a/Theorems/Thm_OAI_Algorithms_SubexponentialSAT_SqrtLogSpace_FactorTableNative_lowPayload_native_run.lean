-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableNative_lowPayload_native_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.lowPayload_native_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:07:34.677464+00:00
-- url     : https://prove2.me/theorems/9ce51423-ddc5-43c7-b51c-f35b39b01b4a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.lowPayload_native_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.lowPayload_native_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative`, with `open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram`, `open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram`, `open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes`):
--
--   ```lean
--   theorem lowPayload_native_run {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
--       (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
--       (u J n f S j : ℕ) (hu : 0 < u) (hJ : 0 < J)
--       (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
--       (s : FactorTableProgram.OuterStore) (acc : List Bool) (regs : Fin 16 → Bool)
--       (hcommon : StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta
--         (FactorTableProgram.projectBase s) n)
--       (hsource : SourceReady.Input p ps P
--         (projectState id FactorTableProgram.basePort (sourceCallData s j acc regs)) j n f S)
--       (hj : j < n) (hn : n ≤ S) (hf : f ≤ S)
--       (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
--       (hmask : (s 857).length = n) (htmp : s 881 = []) :
--       ∃ xs : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)),
--         xs.length = n ∧
--         LayoutSourceRowsProgram.RowProperty DensePolynomialProgram.Fixed.encode
--           (fun z out => PolynomialExecutorProgram.meaning p.ops out.val =
--             LayoutSourceRowsProgram.sourceRowFamily ps n f j
--               (LayoutSourceRowsProgram.totalPackedSource p P) z)
--           ((p.R+1)*(d*baseWidth 3 p.t)) 0 xs ∧
--         let pairs := pairChoice xs (s 546)
--         let source := QueryProducerSpace.emittedSource p.t p.model p.modulus p.cache
--           J (p.R+1) theta pairs
--         let result := MomentsProgram.Normalize.run 3 p.t p.modulus p.cache
--           (HeadEvaluation.specializeEntries (Squarefree.decodeMask pairs.length (s 857)) source) []
--         ∃ k rf, k ≤ Source.nativeSourceWorkPolynomial p S + 1 +
--             (7*n+5+FactorTableProgram.specializeBudget p.t d u J (p.R+1) pairs.length
--               (1+pairs.length*(J-1)) (MomentsProgram.Product.bytes source).length
--               (FactorTableProgram.projectInner
--                 (Function.update (sourceCallData s j acc regs).stacks 545
--                   (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs)))) ∧
--           TruncatedRingProgram.Good ∅ u J result ∧
--           Eval FactorTableProgram.lowPayload k (sourceCallData s j acc regs)
--             (⟨rf,Function.update
--               (Function.update (sourceCallData s j acc regs).stacks 545
--                 (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs))
--               557 (MomentsProgram.Product.bytes result)⟩ : FactorTableProgram.OuterData)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowProperty` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.decodeMask` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.OuterStore` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.basePort` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowFamily` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.projectBase` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation.specializeEntries` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.stream` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.projectInner` (definitions bundle `OAIQ081S074` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.Array` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.encode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.run` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.meaning` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.pairChoice` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeBudget` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.emittedSource` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.StagedInput` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.sourceCallData` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.totalPackedSource` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input` (definitions bundle `OAIQ081S170` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.nativeSourceWorkPolynomial` (definitions bundle `OAIQ081S176` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.lowPayload` (definitions bundle `OAIQ081S189` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.native_literal` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.lowPayload_native_run)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}

theorem lowPayload_native_run {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f S j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (s : FactorTableProgram.OuterStore) (acc : List Bool) (regs : Fin 16 → Bool)
    (hcommon : StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta
      (FactorTableProgram.projectBase s) n)
    (hsource : SourceReady.Input p ps P
      (projectState id FactorTableProgram.basePort (sourceCallData s j acc regs)) j n f S)
    (hj : j < n) (hn : n ≤ S) (hf : f ≤ S)
    (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (hmask : (s 857).length = n) (htmp : s 881 = []) :
    ∃ xs : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)),
      xs.length = n ∧
      LayoutSourceRowsProgram.RowProperty DensePolynomialProgram.Fixed.encode
        (fun z out => PolynomialExecutorProgram.meaning p.ops out.val =
          LayoutSourceRowsProgram.sourceRowFamily ps n f j
            (LayoutSourceRowsProgram.totalPackedSource p P) z)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 xs ∧
      let pairs := pairChoice xs (s 546)
      let source := QueryProducerSpace.emittedSource p.t p.model p.modulus p.cache
        J (p.R+1) theta pairs
      let result := MomentsProgram.Normalize.run 3 p.t p.modulus p.cache
        (HeadEvaluation.specializeEntries (Squarefree.decodeMask pairs.length (s 857)) source) []
      ∃ k rf, k ≤ Source.nativeSourceWorkPolynomial p S + 1 +
          (7*n+5+FactorTableProgram.specializeBudget p.t d u J (p.R+1) pairs.length
            (1+pairs.length*(J-1)) (MomentsProgram.Product.bytes source).length
            (FactorTableProgram.projectInner
              (Function.update (sourceCallData s j acc regs).stacks 545
                (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs)))) ∧
        TruncatedRingProgram.Good ∅ u J result ∧
        Eval FactorTableProgram.lowPayload k (sourceCallData s j acc regs)
          (⟨rf,Function.update
            (Function.update (sourceCallData s j acc regs).stacks 545
              (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs))
            557 (MomentsProgram.Product.bytes result)⟩ : FactorTableProgram.OuterData) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

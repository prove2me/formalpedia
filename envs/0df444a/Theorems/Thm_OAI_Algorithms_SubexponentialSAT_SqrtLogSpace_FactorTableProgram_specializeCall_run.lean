-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableProgram_specializeCall_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:55:50.810378+00:00
-- url     : https://prove2.me/theorems/304d6bec-5090-475b-9a0e-0898f8953eb4
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableSpecialization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableSpecialization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram`, with `open OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives`, `open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing`):
--
--   ```lean
--   theorem specializeCall_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
--       (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
--       (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
--       (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
--       (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
--       (a : OuterData) (low : Fin 256 → List Bool)
--       (hinput : PerturbationAssembly.LowInput t model M cache J N theta rows low)
--       (hout : low 217 = []) (U : Finset (Fin rows.length))
--       (hmask : a.stacks 857 = Squarefree.encodeMask U) (htmp : a.stacks 881 = [])
--       (hs : ∀ i, a.stacks (joinedPort i) =
--         (QueryProducerSpace.Native.joinedState a.regs low
--           (QueryProducerSpace.Native.emptyHigh [])).stacks i) :
--       let source := QueryProducerSpace.emittedSource t model M cache J N theta rows
--       let result := MomentsProgram.Normalize.run 3 t M cache
--         (HeadEvaluation.specializeEntries U source) []
--       ∃ k rf, k ≤ 7*(a.stacks 857).length+5+
--         specializeBudget t d u J N rows.length (1+rows.length*(J-1))
--           (MomentsProgram.Product.bytes source).length low ∧
--         TruncatedRingProgram.Good ∅ u J result ∧
--         Eval specializeCall k a
--           (⟨rf, Function.update a.stacks 557 (MomentsProgram.Product.bytes result)⟩ : OuterData)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.encodeMask` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.joinedPort` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation.specializeEntries` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.Array` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.run` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeBudget` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.OuterData` (definitions bundle `OAIQ081S142` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.emittedSource` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.Native.emptyHigh` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.Native.joinedState` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall` (definitions bundle `OAIQ081S188` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.lowPayload_native_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableSpecialization.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall_run)

import Mathlib
import Definitions.Def_OAIQ081S188

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem specializeCall_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
    (a : OuterData) (low : Fin 256 → List Bool)
    (hinput : PerturbationAssembly.LowInput t model M cache J N theta rows low)
    (hout : low 217 = []) (U : Finset (Fin rows.length))
    (hmask : a.stacks 857 = Squarefree.encodeMask U) (htmp : a.stacks 881 = [])
    (hs : ∀ i, a.stacks (joinedPort i) =
      (QueryProducerSpace.Native.joinedState a.regs low
        (QueryProducerSpace.Native.emptyHigh [])).stacks i) :
    let source := QueryProducerSpace.emittedSource t model M cache J N theta rows
    let result := MomentsProgram.Normalize.run 3 t M cache
      (HeadEvaluation.specializeEntries U source) []
    ∃ k rf, k ≤ 7*(a.stacks 857).length+5+
      specializeBudget t d u J N rows.length (1+rows.length*(J-1))
        (MomentsProgram.Product.bytes source).length low ∧
      TruncatedRingProgram.Good ∅ u J result ∧
      Eval specializeCall k a
        (⟨rf, Function.update a.stacks 557 (MomentsProgram.Product.bytes result)⟩ : OuterData) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

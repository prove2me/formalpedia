-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_prepareLocalInverse_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:23:36.314469+00:00
-- url     : https://prove2.me/theorems/ed3290a9-b5a7-4d2d-9539-751f255552c1
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramExecutionPrepare.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramExecutionPrepare.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl`):
--
--   ```lean
--   theorem prepareLocalInverse_run {C P : Type*} (base : Store)
--       (encC : C → List Bool) (encP : P → List Bool) (constant : C → P)
--       (sm sa : Code) (cm ca : C → C → C) (Km Ka W V J U : ℕ)
--       (hsm : ServiceSpec base encC sm cm Km) (hsa : ServiceSpec base encC sa ca Ka)
--       (hcwidth : ∀ c, (encC c).length = W) (hpwidth : ∀ p, (encP p).length ≤ V)
--       (zero one minusOne c : C) (factor : P) (rest : List Bool)
--       (hconstant : ∀ a, encP (constant a) =
--         DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC zero) J)
--       (hhead : encP factor = encC c ++ rest)
--       (s : Store) (hf : LowFrame base s)
--       (hfactor : s 240 = encP factor) (hzero : s 104 = encC zero)
--       (hzeroBits : encC zero = List.replicate W false)
--       (hone : s 207 = encC one) (hminus : s 211 = encC minusOne)
--       (hJ : s 243 = List.replicate J true) (hpolyZero : s 192 = encP (constant zero))
--       (hcursor : ∀ i ∈ ([217,229] : List (Fin 256)), (s i).length ≤ U)
--       (hclean : ∀ i ∈ ([100,101,102,107,108,120,121,122,205,208,220,222,223,
--           227,228,241,242,244,245,246,247] : List (Fin 256)), s i = []) :
--       let a := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
--       ExecutesIn (executionPreparation sm sa)
--         (preparationBudget (s 209).length (s 212).length J Km Ka W V U) s
--         (preparedLocal (SubexpLocalCRTSetup.cleared [217,229] s)
--           (encP factor) (encP (constant one)) (encP (constant a))
--           (encP (constant (cm a minusOne))) (encP (constant zero)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.LowFrame` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Store` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseValue` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.preparationBudget` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor.Counter.paddedBits` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Code` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLocalCRTSetup.cleared` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.preparedLocal` (definitions bundle `OAIQ081S028` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.ServiceSpec` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.executionPreparation` (definitions bundle `OAIQ081S118` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramExecutionPrepare.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse_run)

import Mathlib
import Definitions.Def_OAIQ081S118

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem prepareLocalInverse_run {C P : Type*} (base : Store)
    (encC : C → List Bool) (encP : P → List Bool) (constant : C → P)
    (sm sa : Code) (cm ca : C → C → C) (Km Ka W V J U : ℕ)
    (hsm : ServiceSpec base encC sm cm Km) (hsa : ServiceSpec base encC sa ca Ka)
    (hcwidth : ∀ c, (encC c).length = W) (hpwidth : ∀ p, (encP p).length ≤ V)
    (zero one minusOne c : C) (factor : P) (rest : List Bool)
    (hconstant : ∀ a, encP (constant a) =
      DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC zero) J)
    (hhead : encP factor = encC c ++ rest)
    (s : Store) (hf : LowFrame base s)
    (hfactor : s 240 = encP factor) (hzero : s 104 = encC zero)
    (hzeroBits : encC zero = List.replicate W false)
    (hone : s 207 = encC one) (hminus : s 211 = encC minusOne)
    (hJ : s 243 = List.replicate J true) (hpolyZero : s 192 = encP (constant zero))
    (hcursor : ∀ i ∈ ([217,229] : List (Fin 256)), (s i).length ≤ U)
    (hclean : ∀ i ∈ ([100,101,102,107,108,120,121,122,205,208,220,222,223,
        227,228,241,242,244,245,246,247] : List (Fin 256)), s i = []) :
    let a := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
    ExecutesIn (executionPreparation sm sa)
      (preparationBudget (s 209).length (s 212).length J Km Ka W V U) s
      (preparedLocal (SubexpLocalCRTSetup.cleared [217,229] s)
        (encP factor) (encP (constant one)) (encP (constant a))
        (encP (constant (cm a minusOne))) (encP (constant zero))) := by
  sorry

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

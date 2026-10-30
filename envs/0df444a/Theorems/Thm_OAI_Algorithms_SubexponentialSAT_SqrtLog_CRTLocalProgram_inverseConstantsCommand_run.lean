-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_inverseConstantsCommand_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseConstantsCommand_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:06:51.008597+00:00
-- url     : https://prove2.me/theorems/a274593b-7c35-4d3b-b225-69de1fa94c08
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseConstantsCommand_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseConstantsCommand_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramInverseConstants.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramInverseConstants.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl`):
--
--   ```lean
--   theorem inverseConstantsCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
--       (sm sa : Code) (cm ca : C → C → C) (Km Ka W J : ℕ)
--       (hm : ServiceSpec base encode sm cm Km) (ha : ServiceSpec base encode sa ca Ka)
--       (hw : ∀ a, (encode a).length = W)
--       (s : Store) (c zero one minusOne : C) (hf : LowFrame base s)
--       (hc : s 205 = encode c) (hz : s 104 = encode zero)
--       (hzbits : encode zero = List.replicate W false)
--       (ho : s 207 = encode one) (hn : s 211 = encode minusOne)
--       (hJ : s 243 = List.replicate J true)
--       (hclean : ∀ i ∈ ([100,101,102,107,108,120,208,220,222,227,228,240,241,244,245,246] : List (Fin 256)),
--         s i = []) :
--       let a := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
--       ExecutesIn (inverseConstantsCommand sm sa)
--         (inverseConstantsBudget (s 209).length (s 212).length J Km Ka W) s
--         (Function.update (Function.update (Function.update s 205 []) 227
--           (DensePolynomialProgram.Constructor.Counter.paddedBits W (encode a) (encode zero) J)) 228
--           (DensePolynomialProgram.Constructor.Counter.paddedBits W (encode (cm a minusOne)) (encode zero) J))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.LowFrame` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Store` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseConstantsBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseValue` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor.Counter.paddedBits` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Code` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.ServiceSpec` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseConstantsCommand` (definitions bundle `OAIQ081S100` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramInverseConstants.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseConstantsCommand_run)

import Mathlib
import Definitions.Def_OAIQ081S100

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem inverseConstantsCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (sm sa : Code) (cm ca : C → C → C) (Km Ka W J : ℕ)
    (hm : ServiceSpec base encode sm cm Km) (ha : ServiceSpec base encode sa ca Ka)
    (hw : ∀ a, (encode a).length = W)
    (s : Store) (c zero one minusOne : C) (hf : LowFrame base s)
    (hc : s 205 = encode c) (hz : s 104 = encode zero)
    (hzbits : encode zero = List.replicate W false)
    (ho : s 207 = encode one) (hn : s 211 = encode minusOne)
    (hJ : s 243 = List.replicate J true)
    (hclean : ∀ i ∈ ([100,101,102,107,108,120,208,220,222,227,228,240,241,244,245,246] : List (Fin 256)),
      s i = []) :
    let a := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
    ExecutesIn (inverseConstantsCommand sm sa)
      (inverseConstantsBudget (s 209).length (s 212).length J Km Ka W) s
      (Function.update (Function.update (Function.update s 205 []) 227
        (DensePolynomialProgram.Constructor.Counter.paddedBits W (encode a) (encode zero) J)) 228
        (DensePolynomialProgram.Constructor.Counter.paddedBits W (encode (cm a minusOne)) (encode zero) J)) := by
  sorry

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

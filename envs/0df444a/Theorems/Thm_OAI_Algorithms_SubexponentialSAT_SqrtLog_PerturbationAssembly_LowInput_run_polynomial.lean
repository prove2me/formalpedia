-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_LowInput_run_polynomial
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run_polynomial
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:54:58.83615+00:00
-- url     : https://prove2.me/theorems/c3e6e1d9-3129-46bc-b98d-0b164cec4e69
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run_polynomial: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run_polynomial` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyLowBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyLowBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl`, `open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`):
--
--   ```lean
--   theorem LowInput.run_polynomial {t d : ℕ} {a : RingModel.Data d}
--       {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
--       {J N : ℕ} {theta : Coeff (baseWidth 3 t) d}
--       {rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)} {s : Store}
--       (h : LowInput t a M cache J N theta rows s) :
--       ExecutesIn prepareLow
--         (lowWorkPolynomial rows.length N J t d ((s 192).length+(s 193).length+(s 243).length)) s
--         (Function.update s 217 (lowOutput t a M cache J N theta rows (s 217)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.Array` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.lowWorkPolynomial` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.lowOutput` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.prepareLow` (definitions bundle `OAIQ081S188` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.low_run_space` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyLowBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run_polynomial)

import Mathlib
import Definitions.Def_OAIQ081S188

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem LowInput.run_polynomial {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {J N : ℕ} {theta : Coeff (baseWidth 3 t) d}
    {rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)} {s : Store}
    (h : LowInput t a M cache J N theta rows s) :
    ExecutesIn prepareLow
      (lowWorkPolynomial rows.length N J t d ((s 192).length+(s 193).length+(s 243).length)) s
      (Function.update s 217 (lowOutput t a M cache J N theta rows (s 217))) := by
  sorry

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

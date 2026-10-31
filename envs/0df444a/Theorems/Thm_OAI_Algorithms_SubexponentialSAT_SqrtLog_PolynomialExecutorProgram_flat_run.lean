-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PolynomialExecutorProgram_flat_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flat_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:38:11.465019+00:00
-- url     : https://prove2.me/theorems/7e0401cb-9986-4f72-84bb-9dcaf90e24e1
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flat_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flat_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PolynomialExecutorProgramFlat.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PolynomialExecutorProgramFlat.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg contextStore)`, `open SubexponentialSAT.SubexpRowPostfixContext (operandStore )`):
--
--   ```lean
--   theorem flat_run {B d : ℕ} (context : Fin 252 → List Bool)
--       (source : List Bool) (out : List (Coeff B d)) (K : ℕ)
--       (h21 : contextStore context 21 = []) (h120 : contextStore context 120 = [])
--       (h240 : contextStore context 240 = [])
--       (hrun : RunsIn program K
--         (physicalCfg (some program.entry) false false false source [] [] context)
--         (physicalCfg none false false false [] (SubexpPostfixControl.operandDepth [out])
--           (Encoding.encodeList DensePolynomialProgram.encode [out]) context)) :
--       ∃ rf, RunsIn flatProgram (K+18*(DensePolynomialProgram.encode out).length+28)
--         (physicalCfg (some flatProgram.entry) false false false source [] [] context)
--         ((⟨rf,Function.update (contextStore context) 240 (DensePolynomialProgram.encode out)⟩ : Data).withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl.operandDepth` (definitions bundle `OAIQ081S022` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.AddService.command` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.command`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.reset`, `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg`, `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flattenCommand` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.contextStore` (definitions bundle `OAIQ081S098` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.encode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mulCommand` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flatProgram` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.program` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.model_flat_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PolynomialExecutorProgramFlat.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flat_run)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S098
import Definitions.Def_OAIQ081S125

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg contextStore)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore )

theorem flat_run {B d : ℕ} (context : Fin 252 → List Bool)
    (source : List Bool) (out : List (Coeff B d)) (K : ℕ)
    (h21 : contextStore context 21 = []) (h120 : contextStore context 120 = [])
    (h240 : contextStore context 240 = [])
    (hrun : RunsIn program K
      (physicalCfg (some program.entry) false false false source [] [] context)
      (physicalCfg none false false false [] (SubexpPostfixControl.operandDepth [out])
        (Encoding.encodeList DensePolynomialProgram.encode [out]) context)) :
    ∃ rf, RunsIn flatProgram (K+18*(DensePolynomialProgram.encode out).length+28)
      (physicalCfg (some flatProgram.entry) false false false source [] [] context)
      ((⟨rf,Function.update (contextStore context) 240 (DensePolynomialProgram.encode out)⟩ : Data).withPC none) := by
  sorry

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

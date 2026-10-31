-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PolynomialExecutorProgram_load_implements
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.load_implements
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:08:38.716552+00:00
-- url     : https://prove2.me/theorems/326278c7-58c3-4874-9e4e-dd14fe55b903
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.load_implements: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.load_implements` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PolynomialExecutorProgramLoad.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PolynomialExecutorProgramLoad.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg LoadImplementsGlobal)`, `open SubexponentialSAT.SubexpRowPostfixContext (operandStore )`):
--
--   ```lean
--   theorem load_implements
--       (hzero : RingProgram.flat ops.zeroRun.1 = List.replicate (d*baseWidth p t) false) :
--       LoadImplementsGlobal DensePolynomialProgram.encode (loadValue ops J)
--         SubexpDenseLiteralPadding.program (loadBound (baseWidth p t) d J) context
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size` and `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RingProgram` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.command`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program` and `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.reset` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.LoadImplementsGlobal` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.encode` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Coeff` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.loadValue` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Ready` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.loadBound` (definitions bundle `OAIQ081S151` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.program_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PolynomialExecutorProgramLoad.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.load_implements)

import Mathlib
import Definitions.Def_OAIQ081S151

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
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg LoadImplementsGlobal)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore )

variable (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (J : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : Ready p t M cache ops table J width frame context)

include H in
theorem load_implements
    (hzero : RingProgram.flat ops.zeroRun.1 = List.replicate (d*baseWidth p t) false) :
    LoadImplementsGlobal DensePolynomialProgram.encode (loadValue ops J)
      SubexpDenseLiteralPadding.program (loadBound (baseWidth p t) d J) context := by
  sorry

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

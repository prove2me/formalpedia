-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PolynomialExecutorProgram_mul_implements
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.mul_implements
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:10:02.729353+00:00
-- url     : https://prove2.me/theorems/60e18011-49d0-41f8-bcb3-ff5fbb43cf1e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.mul_implements: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.mul_implements` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PolynomialExecutorProgramServices.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PolynomialExecutorProgramServices.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg ImplementsOnGlobal LoadImplementsGlobal)`, `open SubexponentialSAT.SubexpRowPostfixContext (operandStore preparedStore )`):
--
--   ```lean
--   theorem mul_implements (hB : 0 < baseWidth p t)
--       (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
--       (hadd : ∀ a b, (ops.addRun a b).1 =
--         (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
--       (hmul : ∀ a b, (ops.mulRun a b).1 =
--         (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1) :
--       ImplementsOnGlobal (fun P : List (Coeff (baseWidth p t) d) => P.length = J)
--         DensePolynomialProgram.encode (mulValue ops J) true mulProgram
--         (fun _ _ => binaryBound (DensePolynomialProgram.nativeMulBudget J d (baseWidth p t))
--           (J*(d*baseWidth p t))) context
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RingProgram` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.nativeMulBudget` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.binaryBound` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.addRun` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.mulRun` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.scalarProgram` (definitions bundle `OAIQ081S068` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.command` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.ImplementsOnGlobal` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.encode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mulCommand` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.mulProgram` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.mulValue` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Ready` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.program_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PolynomialExecutorProgramServices.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.mul_implements)

import Mathlib
import Definitions.Def_SubexponentialSAT
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
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg ImplementsOnGlobal LoadImplementsGlobal)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore preparedStore )

variable (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (J : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : Ready p t M cache ops table J width frame context)

include H in
theorem mul_implements (hB : 0 < baseWidth p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1) :
    ImplementsOnGlobal (fun P : List (Coeff (baseWidth p t) d) => P.length = J)
      DensePolynomialProgram.encode (mulValue ops J) true mulProgram
      (fun _ _ => binaryBound (DensePolynomialProgram.nativeMulBudget J d (baseWidth p t))
        (J*(d*baseWidth p t))) context := by
  sorry

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

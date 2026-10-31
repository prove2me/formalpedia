-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_evaluateModel_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluateModel_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:58:32.485519+00:00
-- url     : https://prove2.me/theorems/689030c6-6a29-478b-8e7b-71c4fffd80ed
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluateModel_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluateModel_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramModel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramModel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram`, with `open SubexponentialSAT BitProgram StructuredCalls`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg contextStore)`, `open SubexponentialSAT.SubexpRowPostfixContext (operandStore )`):
--
--   ```lean
--   theorem evaluateModel_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
--       (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
--       (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
--       (J : ℕ) (width : List Bool) (frame : Fin 6 → List Bool) (s : Store)
--       (H : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
--         (HornerProgram.modelTable t a M cache) J width frame
--           (executionContext (evaluationInput s)))
--       (e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)))
--       (hsource : s 333=(SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile).reverse)
--       (h27 : s 27=[]) (h28 : s 28=[]) (h29 : s 29=[])
--       (h335 : s 335=[]) (h336 : s 336=[]) :
--       ∃ out : List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d), out.length=J ∧
--         PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
--           Truncation.trunc J ((e.map (PolynomialExecutorProgram.meaning
--             (RingProgram.modelRing t ht hd a M cache))).eval) ∧
--         ExecutesIn (evaluateRow PolynomialExecutorProgram.flatProgram)
--           (300000*((s 333).length+1)*(J+1)^3*(d+1)^3*(baseWidth 3 t+1)^2+
--             18*(J*(d*baseWidth 3 t))+46+6*(s 21).length+6*(s 26).length+
--             3*(s 333).length+15) s
--           (Function.update (Function.update s 333 []) 240 (DensePolynomialProgram.encode out))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.compile`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.eval`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.map` and `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.Truncation.trunc` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Store` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluationInput` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl.serializeCode` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.AddService.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.command`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.reset`, `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.executionContext` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flattenCommand` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.encode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mulCommand` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.modelTable` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.ExecutesIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluateRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flatProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.meaning` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.program` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Ready` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowWith_run` and `OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRows_present_model` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramModel.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluateModel_run)

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

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg contextStore)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore )

theorem evaluateModel_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (J : ℕ) (width : List Bool) (frame : Fin 6 → List Bool) (s : Store)
    (H : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) J width frame
        (executionContext (evaluationInput s)))
    (e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)))
    (hsource : s 333=(SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile).reverse)
    (h27 : s 27=[]) (h28 : s 28=[]) (h29 : s 29=[])
    (h335 : s 335=[]) (h336 : s 336=[]) :
    ∃ out : List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d), out.length=J ∧
      PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
        Truncation.trunc J ((e.map (PolynomialExecutorProgram.meaning
          (RingProgram.modelRing t ht hd a M cache))).eval) ∧
      ExecutesIn (evaluateRow PolynomialExecutorProgram.flatProgram)
        (300000*((s 333).length+1)*(J+1)^3*(d+1)^3*(baseWidth 3 t+1)^2+
          18*(J*(d*baseWidth 3 t))+46+6*(s 21).length+6*(s 26).length+
          3*(s 333).length+15) s
        (Function.update (Function.update s 333 []) 240 (DensePolynomialProgram.encode out)) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

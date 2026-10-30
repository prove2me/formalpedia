-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpRowPostfixInterpreter_global_complete_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.global_complete_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:04:57.578825+00:00
-- url     : https://prove2.me/theorems/af064f36-2227-4d69-a55d-796f450e7a7a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.global_complete_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.global_complete_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SubexpRowPostfixInterpreter.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpRowPostfixInterpreter.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter`, with `open BitProgram`, `open SubexpPostfixControl (serializeCode operandDepth)`, `open SubexpPostfixInterpreter (cfg)`, `open SubexpPostfixGlobal (reindexCfg )`, `open SubexpProjectedInterpreter (exprCost LoadImplements ImplementsOn Validity)`):
--
--   ```lean
--   theorem global_complete_runsIn {R : Type*} [Add R] [Mul R] {a b c : ℕ}
--       (add : Program 16 256 a) (mul : Program 16 256 b) (loader : Program 16 256 c)
--       (encode : R → List Bool) (project : R → R) (valid : R → Prop)
--       (addBound mulBound : R → R → ℕ) (loadBound : R → ℕ) (context : Fin 252 → List Bool)
--       (ha : ImplementsOnGlobal valid encode (· + ·) false add addBound context)
--       (hm : ImplementsOnGlobal valid encode (· * ·) true mul mulBound context)
--       (hl : LoadImplementsGlobal encode project loader loadBound context)
--       (hvalid : Validity valid project) (e : Algorithm.Expr R) :
--       RunsIn (globalProgram add mul loader) (exprCost encode addBound mulBound project loadBound e + 5)
--         (physicalCfg (some (globalProgram add mul loader).entry) false false false
--           (serializeCode encode e.compile) [] [] context)
--         (physicalCfg none false false false [] (operandDepth [(e.map project).eval])
--           (Encoding.encodeList encode [(e.map project).eval]) context)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.compile`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.eval` and `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.map` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl.operandDepth` and `OAI.Algorithms.SubexponentialSAT.SubexpProjectedInterpreter.Validity` (definitions bundle `OAIQ081S022` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl.serializeCode` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpProjectedInterpreter.exprCost` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.globalProgram` and `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.ImplementsOnGlobal` and `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.LoadImplementsGlobal` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.program_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpRowPostfixInterpreter.lean (declaration OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.global_complete_runsIn)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpRowPostfixInterpreter

open BitProgram
open SubexpPostfixControl (serializeCode operandDepth)
open SubexpPostfixInterpreter (cfg)
open SubexpPostfixGlobal (reindexCfg )
open SubexpProjectedInterpreter (exprCost LoadImplements ImplementsOn Validity)

theorem global_complete_runsIn {R : Type*} [Add R] [Mul R] {a b c : ℕ}
    (add : Program 16 256 a) (mul : Program 16 256 b) (loader : Program 16 256 c)
    (encode : R → List Bool) (project : R → R) (valid : R → Prop)
    (addBound mulBound : R → R → ℕ) (loadBound : R → ℕ) (context : Fin 252 → List Bool)
    (ha : ImplementsOnGlobal valid encode (· + ·) false add addBound context)
    (hm : ImplementsOnGlobal valid encode (· * ·) true mul mulBound context)
    (hl : LoadImplementsGlobal encode project loader loadBound context)
    (hvalid : Validity valid project) (e : Algorithm.Expr R) :
    RunsIn (globalProgram add mul loader) (exprCost encode addBound mulBound project loadBound e + 5)
      (physicalCfg (some (globalProgram add mul loader).entry) false false false
        (serializeCode encode e.compile) [] [] context)
      (physicalCfg none false false false [] (operandDepth [(e.map project).eval])
        (Encoding.encodeList encode [(e.map project).eval]) context) := by
  sorry

end SubexponentialSAT.SubexpRowPostfixInterpreter

end OAI.Algorithms
end

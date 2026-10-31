-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PolynomialExecutorProgram_evaluate_full
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_full
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:37:56.287415+00:00
-- url     : https://prove2.me/theorems/5f1e13a8-f706-4ac5-9eb8-012d1c59558e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_full: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_full` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PolynomialExecutorProgramBasic.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PolynomialExecutorProgramBasic.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram`, with `open SubexponentialSAT.SubexpSymbolicCost`):
--
--   ```lean
--   theorem evaluate_full {C R : Type*} [CommRing R] (ops : RepresentedRing C R)
--       (J : ℕ) (e : SubexponentialSAT.Algorithm.Expr (List C))
--       (hdegree : ((e.map (meaning ops)).eval).natDegree < J) :
--       meaning ops (evaluate ops.program J e) = (e.map (meaning ops)).eval
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.eval` and `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.map` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing.program` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.meaning` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate` (definitions bundle `OAIQ081S136` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.typed_row_contract` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PolynomialExecutorProgramBasic.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_full)

import Mathlib
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT.SubexpSymbolicCost

theorem evaluate_full {C R : Type*} [CommRing R] (ops : RepresentedRing C R)
    (J : ℕ) (e : SubexponentialSAT.Algorithm.Expr (List C))
    (hdegree : ((e.map (meaning ops)).eval).natDegree < J) :
    meaning ops (evaluate ops.program J e) = (e.map (meaning ops)).eval := by
  sorry

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

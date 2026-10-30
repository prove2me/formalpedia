-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgramScalar_multiply_eval_total
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:53:25.082533+00:00
-- url     : https://prove2.me/theorems/397394b6-493f-4854-86d0-e2b159e28ab9
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarStep.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarStep.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.SqrtLog.RowSelectionProgram`):
--
--   ```lean
--   theorem multiply_eval_total (regs : Fin 8 → Bool) (acc work next : WordPair)
--       (queue : List Bool) :
--       ∃ t ≤ 25000*(pairLength work+pairLength next+3)^2+2,
--       ∃ r result, Eval multiply t (state regs acc work next queue)
--         (state r acc result ([],[]) queue) ∧
--         pairValue result = pairValue work * pairValue next ∧
--         wordTotal result = wordTotal work * wordTotal next ∧
--         pairLength result ≤ 2*(pairLength work+pairLength next)+6
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.wordTotal` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.state` (definitions bundle `OAIQ081S071` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply` (definitions bundle `OAIQ081S073` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarStep.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total)

import Mathlib
import Definitions.Def_OAIQ081S057
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S073

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem multiply_eval_total (regs : Fin 8 → Bool) (acc work next : WordPair)
    (queue : List Bool) :
    ∃ t ≤ 25000*(pairLength work+pairLength next+3)^2+2,
    ∃ r result, Eval multiply t (state regs acc work next queue)
      (state r acc result ([],[]) queue) ∧
      pairValue result = pairValue work * pairValue next ∧
      wordTotal result = wordTotal work * wordTotal next ∧
      pairLength result ≤ 2*(pairLength work+pairLength next)+6 := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

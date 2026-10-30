-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram_loop_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loop_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:02:37.08429+00:00
-- url     : https://prove2.me/theorems/102e00fc-f8ad-45c2-8fdf-a1cbfaf0b818
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loop_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loop_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram`, `open SubexponentialSAT.Subexp.MatrixParityProgram (toggle)`):
--
--   ```lean
--   theorem loop_eval (c : Cache) (regs : Fin 9 → Bool)
--       (counter hindex kindex buffer queue parity : List Bool)
--       (hu : c.Uniform) (hf : c.Fits (counter.length+kindex.length))
--       (hlen : hindex.length = counter.length) :
--       ∃ r, r 8 = toggle counter.length (regs 8) ∧
--         Eval loop (loopCost counter.length kindex.length c.width.length (pairLength c.power))
--           (cacheState c regs counter hindex kindex buffer queue parity)
--           (cacheState c r [] [] (List.replicate counter.length true++kindex)
--             ((preparedRecords c (regs 8) counter.length kindex.length).reverse++buffer) queue parity)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loopCost` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixParityProgram.toggle` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Fits` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Uniform` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loop` (definitions bundle `OAIQ081S073` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.preparedRecords` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.cacheState` (definitions bundle `OAIQ081S091` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loop_eval)

import Mathlib
import Definitions.Def_OAIQ081S091

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open SubexponentialSAT.Subexp.MatrixParityProgram (toggle)

theorem loop_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool)
    (hu : c.Uniform) (hf : c.Fits (counter.length+kindex.length))
    (hlen : hindex.length = counter.length) :
    ∃ r, r 8 = toggle counter.length (regs 8) ∧
      Eval loop (loopCost counter.length kindex.length c.width.length (pairLength c.power))
        (cacheState c regs counter hindex kindex buffer queue parity)
        (cacheState c r [] [] (List.replicate counter.length true++kindex)
          ((preparedRecords c (regs 8) counter.length kindex.length).reverse++buffer) queue parity) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end

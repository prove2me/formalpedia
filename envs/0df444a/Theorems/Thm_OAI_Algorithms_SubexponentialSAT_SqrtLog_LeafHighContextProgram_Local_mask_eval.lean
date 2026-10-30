-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHighContextProgram_Local_mask_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.mask_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:32:36.794119+00:00
-- url     : https://prove2.me/theorems/96bc3d03-d9d4-4fef-b040-3f76f3e3d7cb
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.mask_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.mask_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHighContextProgramMask.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHighContextProgramMask.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.Subexp.BlockSearchPreparation`):
--
--   ```lean
--   theorem mask_eval (regs : Fin 4 → Bool) (counter mask : List Bool) :
--       ∃ n rf, n ≤ 10*mask.length+9 ∧ Eval maskStep n
--         (state regs counter mask [] [] [] [] [] [] [] [])
--         (state rf counter mask mask.reverse [] [] [] [] [] [] [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.maskStep` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.state` (definitions bundle `OAIQ081S126` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHighContextProgramMask.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.mask_eval)

import Mathlib
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S126

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

theorem mask_eval (regs : Fin 4 → Bool) (counter mask : List Bool) :
    ∃ n rf, n ≤ 10*mask.length+9 ∧ Eval maskStep n
      (state regs counter mask [] [] [] [] [] [] [] [])
      (state rf counter mask mask.reverse [] [] [] [] [] [] []) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

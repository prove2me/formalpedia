-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadAcceptedProgram_register_frame
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram.register_frame
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:12:46.400673+00:00
-- url     : https://prove2.me/theorems/5f884228-99a7-4013-9bf9-ce35f7384fc0
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram.register_frame: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram.register_frame` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedFrames.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedFrames.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram`, with `open OAI BitProgram StructuredCalls CommandRegisterFrames`):
--
--   ```lean
--   theorem register_frame {steps : ℕ}
--       {a b : Cfg 40 896 (size (HeadSumAssembly.head HeadSumAssembly.accepted) + 1)}
--       (ht : Trace program steps a b) (i : Fin 40) (hi : 16 ≤ i.val) :
--       b.regs i = a.regs i
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace` and `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly.head` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram.program` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly.accepted` (definitions bundle `OAIQ081S191` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedFrames.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram.register_frame)

import Mathlib
import Definitions.Def_OAIQ081S191

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram
open OAI BitProgram StructuredCalls CommandRegisterFrames

theorem register_frame {steps : ℕ}
    {a b : Cfg 40 896 (size (HeadSumAssembly.head HeadSumAssembly.accepted) + 1)}
    (ht : Trace program steps a b) (i : Fin 40) (hi : 16 ≤ i.val) :
    b.regs i = a.regs i := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram
end

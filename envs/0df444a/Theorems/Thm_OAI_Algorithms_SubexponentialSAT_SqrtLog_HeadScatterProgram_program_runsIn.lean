-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HeadScatterProgram_program_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:00:10.766503+00:00
-- url     : https://prove2.me/theorems/a33d099b-cc41-4d0a-97ea-5948b66f97ed
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HeadScatterProgramRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HeadScatterProgramRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram`, with `open SubexponentialSAT BitProgram StructuredCalls`):
--
--   ```lean
--   theorem program_runsIn (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) (bits : List Bool)
--       (hlen : js.length=bits.length) (hb : ∀ j ∈ js,j < n) :
--       ∃ rf, RunsIn program (100*(n+1)*(js.length+1))
--         ((input regs js bits n).withPC (some program.entry))
--         ((result rf js bits n).withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.result` (definitions bundle `OAIQ081S085` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.prepareHead_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HeadScatterProgramRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program_runsIn)

import Mathlib
import Definitions.Def_OAIQ081S085

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem program_runsIn (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) (bits : List Bool)
    (hlen : js.length=bits.length) (hb : ∀ j ∈ js,j < n) :
    ∃ rf, RunsIn program (100*(n+1)*(js.length+1))
      ((input regs js bits n).withPC (some program.entry))
      ((result rf js bits n).withPC none) := by
  sorry

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

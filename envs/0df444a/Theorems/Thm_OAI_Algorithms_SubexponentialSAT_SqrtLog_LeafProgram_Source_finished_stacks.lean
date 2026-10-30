-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Source_finished_stacks
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.finished_stacks
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:29:59.696103+00:00
-- url     : https://prove2.me/theorems/41fc6751-cf8e-450f-82c1-545e0b054372
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.finished_stacks: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.finished_stacks` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramSourceFrame.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramSourceFrame.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage`):
--
--   ```lean
--   theorem finished_stacks (a : Data) (b : State 16 340)
--       (hf : CoreFrame a b)
--       (hlow : ∀ i ∈ SourceStaging.lowClearPorts, a.stacks i = [])
--       (hextra : ∀ i ∈ SourceControls.extraPorts, a.stacks i = [])
--       (hb : ∀ i ∈ SourceStaging.backupPorts, a.stacks i = []) :
--       (finished a b).stacks = Function.update a.stacks 545 (b.stacks 205)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceControls.extraPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.backupPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.lowClearPorts` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.CoreFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.finished` (definitions bundle `OAIQ081S159` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramSourceFrame.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.finished_stacks)

import Mathlib
import Definitions.Def_OAIQ081S159

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem finished_stacks (a : Data) (b : State 16 340)
    (hf : CoreFrame a b)
    (hlow : ∀ i ∈ SourceStaging.lowClearPorts, a.stacks i = [])
    (hextra : ∀ i ∈ SourceControls.extraPorts, a.stacks i = [])
    (hb : ∀ i ∈ SourceStaging.backupPorts, a.stacks i = []) :
    (finished a b).stacks = Function.update a.stacks 545 (b.stacks 205) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

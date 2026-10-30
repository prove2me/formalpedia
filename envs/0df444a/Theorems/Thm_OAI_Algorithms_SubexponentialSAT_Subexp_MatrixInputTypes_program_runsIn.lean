-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_MatrixInputTypes_program_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes.program_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:55:48.704195+00:00
-- url     : https://prove2.me/theorems/13260625-af2d-496d-a928-cc87a137b22d
-- title:
--   OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes.program_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes.program_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/Subexp/MatrixInputTypes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/MatrixInputTypes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes`, with `open BitProgram StructuredCalls MulticolorTypes ReadPlan MatrixInputProgram`):
--
--   ```lean
--   theorem program_runsIn (i : Fin Δ) (u y : UniversalType r Q Δ) (regs : Fin 8 → Bool) :
--       RunsIn MatrixInputProgram.program
--         (36 * CollisionProgram.typeWidth r Q Δ +
--           4 * (i.val + 1) * (14 * (Q * r) + 17) + 203 * (Q * r) + 265)
--         ((input i u y regs).withPC (some MatrixInputProgram.program.entry))
--         ((output i u y regs).withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram.typeWidth` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputProgram.command` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputProgram.program` (definitions bundle `OAIQ081S056` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes.input` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes.output` (definitions bundle `OAIQ081S081` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanStage_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_mismatch_branch` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guard_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/MatrixInputTypes.lean (declaration OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes.program_runsIn)

import Mathlib
import Definitions.Def_OAIQ081S081

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.Subexp.MatrixInputTypes

open BitProgram StructuredCalls MulticolorTypes ReadPlan MatrixInputProgram

variable {r Q Δ : ℕ}

theorem program_runsIn (i : Fin Δ) (u y : UniversalType r Q Δ) (regs : Fin 8 → Bool) :
    RunsIn MatrixInputProgram.program
      (36 * CollisionProgram.typeWidth r Q Δ +
        4 * (i.val + 1) * (14 * (Q * r) + 17) + 203 * (Q * r) + 265)
      ((input i u y regs).withPC (some MatrixInputProgram.program.entry))
      ((output i u y regs).withPC none) := by
  sorry

end SubexponentialSAT.Subexp.MatrixInputTypes

end OAI.Algorithms
end

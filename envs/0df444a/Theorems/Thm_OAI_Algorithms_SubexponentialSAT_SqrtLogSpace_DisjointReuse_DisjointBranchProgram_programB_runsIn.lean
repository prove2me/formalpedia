-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DisjointBranchProgram_programB_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.programB_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:14:45.039118+00:00
-- url     : https://prove2.me/theorems/32fed877-2166-4112-98a7-cf46103bec75
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.programB_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.programB_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointSparsifyProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointSparsifyProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram`, with `open OAI.Algorithms.SubexponentialSAT.SAT`, `open BitProgram StructuredCalls`):
--
--   ```lean
--   theorem programB_runsIn (F S : List (List ℕ)) (H : List ℕ) (d : State 15 16)
--       (hcore : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
--       (hselected : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
--       (hsource : d.stacks 13 = ExecCoreChildProgram.formulaCode F)
--       (hready : ExecCoreChildProgram.InputReady d) :
--       ∃ e : State 15 16, SubexpNormalizationProgram.Ready e ∧
--         e.stacks 13 = ExecCoreChildProgram.formulaCode
--           (resultB SubexpFrontend.negateCode F S H) ∧
--         RunsIn programB (600000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2)
--           (d.withPC (some programB.entry)) (e.withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpFrontend.negateCode` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.clauseCode`, `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.formulaCode` and `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.inputVolume` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.resultB` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.InputReady` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.Ready` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.commandB` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.programB` (definitions bundle `OAIQ081S115` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.program_runsIn` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointSparsifyProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.programB_runsIn)

import Mathlib
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

open BitProgram StructuredCalls

theorem programB_runsIn (F S : List (List ℕ)) (H : List ℕ) (d : State 15 16)
    (hcore : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hselected : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hsource : d.stacks 13 = ExecCoreChildProgram.formulaCode F)
    (hready : ExecCoreChildProgram.InputReady d) :
    ∃ e : State 15 16, SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = ExecCoreChildProgram.formulaCode
        (resultB SubexpFrontend.negateCode F S H) ∧
      RunsIn programB (600000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2)
        (d.withPC (some programB.entry)) (e.withPC none) := by
  sorry

open ExecBranchControllerSupport

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
end

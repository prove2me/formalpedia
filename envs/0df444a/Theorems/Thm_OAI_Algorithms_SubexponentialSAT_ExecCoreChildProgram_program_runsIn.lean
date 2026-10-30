-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_ExecCoreChildProgram_program_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:57:28.676305+00:00
-- url     : https://prove2.me/theorems/a4b0c846-5a3d-438c-aee6-e450eb53cd76
-- title:
--   OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/ExecCoreChildProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/ExecCoreChildProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram`, with `open BitProgram StructuredCalls`, `open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)`, `open ExecClauseFiltersProgram`):
--
--   ```lean
--   theorem program_runsIn (F selected : List (List ℕ)) (H : List ℕ) (d : Data)
--       (hcore : d.stacks 9 = clauseCode H) (hselected : d.stacks 12 = formulaCode selected)
--       (hsource : d.stacks 13 = formulaCode F) (hready : InputReady d) :
--       ∃ e : Data, SubexpNormalizationProgram.Ready e ∧
--         e.stacks 13 = formulaCode (result F selected H) ∧
--         RunsIn program (3300 * (inputVolume F selected H) ^ 2)
--           (d.withPC (some program.entry)) (e.withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.clauseCode`, `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.formulaCode`, `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.inputVolume` and `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.result` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.Data` (definitions bundle `OAIQ081S046` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.InputReady` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.Ready` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.command` and `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program` (definitions bundle `OAIQ081S082` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.program_runsIn` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/ExecCoreChildProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program_runsIn)

import Mathlib
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S082

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ExecCoreChildProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram

theorem program_runsIn (F selected : List (List ℕ)) (H : List ℕ) (d : Data)
    (hcore : d.stacks 9 = clauseCode H) (hselected : d.stacks 12 = formulaCode selected)
    (hsource : d.stacks 13 = formulaCode F) (hready : InputReady d) :
    ∃ e : Data, SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = formulaCode (result F selected H) ∧
      RunsIn program (3300 * (inputVolume F selected H) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  sorry

end SubexponentialSAT.ExecCoreChildProgram

end OAI.Algorithms
end

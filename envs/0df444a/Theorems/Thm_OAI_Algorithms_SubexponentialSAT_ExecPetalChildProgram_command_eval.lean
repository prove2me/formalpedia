-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_ExecPetalChildProgram_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:57:23.070592+00:00
-- url     : https://prove2.me/theorems/e37ab3ef-5d54-4c8f-a178-ab27c8e199ce
-- title:
--   OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/ExecPetalChildProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/ExecPetalChildProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram`, with `open BitProgram StructuredCalls`, `open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)`, `open ExecClauseFiltersProgram`):
--
--   ```lean
--   theorem command_eval (F selected : List (List ℕ)) (H : List ℕ) (d : Data)
--       (hcore : d.stacks 9 = clauseCode H) (hselected : d.stacks 12 = formulaCode selected)
--       (hsource : d.stacks 13 = formulaCode F) (hready : InputReady d) :
--       ∃ n ≤ 19000 * (inputVolume F selected H)^2, ∃ e : Data,
--         Eval command n d e ∧ SubexpNormalizationProgram.Ready e ∧
--         e.stacks 13 = formulaCode (result F selected H)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.clauseCode`, `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.formulaCode`, `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.inputVolume` and `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.result` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.Data` (definitions bundle `OAIQ081S046` of this split); `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.InputReady` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.Ready` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command` (definitions bundle `OAIQ081S082` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.programB_runsIn` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/ExecPetalChildProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval)

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

namespace SubexponentialSAT.ExecPetalChildProgram
open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram

theorem command_eval (F selected : List (List ℕ)) (H : List ℕ) (d : Data)
    (hcore : d.stacks 9 = clauseCode H) (hselected : d.stacks 12 = formulaCode selected)
    (hsource : d.stacks 13 = formulaCode F) (hready : InputReady d) :
    ∃ n ≤ 19000 * (inputVolume F selected H)^2, ∃ e : Data,
      Eval command n d e ∧ SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = formulaCode (result F selected H) := by
  sorry

end SubexponentialSAT.ExecPetalChildProgram

end OAI.Algorithms
end

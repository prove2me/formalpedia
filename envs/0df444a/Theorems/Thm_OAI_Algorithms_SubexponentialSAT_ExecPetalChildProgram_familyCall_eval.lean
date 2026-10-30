-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_ExecPetalChildProgram_familyCall_eval
-- name    : OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.familyCall_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:52:07.461251+00:00
-- url     : https://prove2.me/theorems/920048b3-3f69-4be9-92f8-519a1b91170a
-- title:
--   OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.familyCall_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.familyCall_eval` of [lean/OAI/Algorithms/SubexponentialSAT/ExecPetalChildProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/ExecPetalChildProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram`, with `open BitProgram StructuredCalls`, `open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)`, `open ExecClauseFiltersProgram`):
--
--   ```lean
--   theorem familyCall_eval (selected : Formula) (H : Clause) (regs : Regs)
--       (master parent : List Bool) :
--       ∃ n ≤ 170 * ((encodeClause H).length + 1) * ((encodeFormula selected).length + 1),
--         ∃ rf : Regs, Eval familyCall n
--           (frame regs (encodeFormula selected) (encodeClause H) master parent [])
--           (frame rf [] (encodeClause H) master parent
--             (Encoding.encodeList id (formulaRecords (ExecPetalFamilyProgram.petals selected H)).reverse))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.Regs`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Clause` and `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Formula` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.formulaRecords`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.encodeClause`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.encodeFormula` and `OAI.Algorithms.SubexponentialSAT.ExecPetalFamilyProgram.petals` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.familyCall` and `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.frame` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/ExecPetalChildProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.familyCall_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S067

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

theorem familyCall_eval (selected : Formula) (H : Clause) (regs : Regs)
    (master parent : List Bool) :
    ∃ n ≤ 170 * ((encodeClause H).length + 1) * ((encodeFormula selected).length + 1),
      ∃ rf : Regs, Eval familyCall n
        (frame regs (encodeFormula selected) (encodeClause H) master parent [])
        (frame rf [] (encodeClause H) master parent
          (Encoding.encodeList id (formulaRecords (ExecPetalFamilyProgram.petals selected H)).reverse)) := by
  sorry

end SubexponentialSAT.ExecPetalChildProgram

end OAI.Algorithms
end

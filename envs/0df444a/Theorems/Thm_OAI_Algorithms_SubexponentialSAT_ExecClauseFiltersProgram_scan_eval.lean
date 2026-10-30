-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_ExecClauseFiltersProgram_scan_eval
-- name    : OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.scan_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:56:50.861622+00:00
-- url     : https://prove2.me/theorems/823365e5-6813-4721-b74b-21f75d522cf5
-- title:
--   OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.scan_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.scan_eval` of [lean/OAI/Algorithms/SubexponentialSAT/ExecClauseFiltersProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/ExecClauseFiltersProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram`, with `open BitProgram StructuredCalls`, `open ExecClauseRelationScan (Clause Formula Mode encodeClause encodeFormula test)`):
--
--   ```lean
--   theorem scan_eval (mode : Mode) (F : Formula) (Q : Clause) (regs : Regs)
--       (source output : List Bool) :
--       ∃ (n : ℕ) (rf : Regs), n ≤ ExecClauseRelationScan.Preserving.bound F Q ∧
--         rf 14 = F.any (fun C => test mode C Q) ∧
--         Eval (scan mode) n
--           (state regs (encodeClause Q) [] (encodeFormula F) source output [])
--           (state rf (encodeClause Q) [F.any (fun C => test mode C Q)]
--             (encodeFormula F) source output [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.Regs`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Clause`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Formula`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Mode` and `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.test` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.encodeClause`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.encodeFormula` and `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Preserving.bound` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.state` (definitions bundle `OAIQ081S046` of this split); `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.scan` (definitions bundle `OAIQ081S082` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.absorb_eval`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.program_runsIn` and `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/ExecClauseFiltersProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.scan_eval)

import Mathlib
import Definitions.Def_OAIQ081S082

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ExecClauseFiltersProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula Mode encodeClause encodeFormula test)

theorem scan_eval (mode : Mode) (F : Formula) (Q : Clause) (regs : Regs)
    (source output : List Bool) :
    ∃ (n : ℕ) (rf : Regs), n ≤ ExecClauseRelationScan.Preserving.bound F Q ∧
      rf 14 = F.any (fun C => test mode C Q) ∧
      Eval (scan mode) n
        (state regs (encodeClause Q) [] (encodeFormula F) source output [])
        (state rf (encodeClause Q) [F.any (fun C => test mode C Q)]
          (encodeFormula F) source output []) := by
  sorry

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
end

-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourcePlanLookup_Scan_command_eval_found
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.command_eval_found
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:02:31.711613+00:00
-- url     : https://prove2.me/theorems/5021e9ab-4c0a-4395-baa3-e742872d0397
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.command_eval_found: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.command_eval_found` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourcePlanLookupFound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourcePlanLookupFound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives`):
--
--   ```lean
--   theorem command_eval_found (regs : Fin 16 → Bool) (literal ambient factor query : List Bool)
--       (nodes : List (List Bool)) :
--       ∃ n ≤ SubexpNodeIndexProgram.Internal.budget query nodes, ∃ rf,
--         Eval command n
--           (data regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
--             [] [] query [] [] [] [] [])
--           (data rf literal ambient factor (ProgramEncoding.encodeRecords nodes)
--             (List.replicate (nodes.idxOf query) true) [] query [] [] [] [] []) ∧
--         rf 4=decide (query ∈ nodes)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ProgramEncoding.encodeRecords` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexProgram.Internal.budget` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.command` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.data` (definitions bundle `OAIQ081S091` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.command_eval_found` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourcePlanLookupFound.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.command_eval_found)

import Mathlib
import Definitions.Def_OAIQ081S091

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

namespace Scan
theorem command_eval_found (regs : Fin 16 → Bool) (literal ambient factor query : List Bool)
    (nodes : List (List Bool)) :
    ∃ n ≤ SubexpNodeIndexProgram.Internal.budget query nodes, ∃ rf,
      Eval command n
        (data regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
          [] [] query [] [] [] [] [])
        (data rf literal ambient factor (ProgramEncoding.encodeRecords nodes)
          (List.replicate (nodes.idxOf query) true) [] query [] [] [] [] []) ∧
      rf 4=decide (query ∈ nodes) := by
  sorry

end Scan

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

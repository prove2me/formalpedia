-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourcePlanLookup_Native_command_eval_found
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.command_eval_found
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:02:09.383663+00:00
-- url     : https://prove2.me/theorems/1b0dcc7d-7772-4b39-a611-ff589ba9f020
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.command_eval_found: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.command_eval_found` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourcePlanLookupFound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourcePlanLookupFound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives`):
--
--   ```lean
--   theorem command_eval_found (d : Data) (nodes : List (List Bool))
--       (hmaster : d.stacks 337=ProgramEncoding.encodeRecords nodes) (hclean : Clean d) :
--       ∃ n ≤ budget d nodes, ∃ e : Data,
--         Eval command n d e ∧
--         e.stacks=Function.update d.stacks 304
--           (List.replicate (nodes.idxOf
--             (pairKey (d.stacks 233) (d.stacks 212++d.stacks 216))) true) ∧
--         e.regs 4=decide (pairKey (d.stacks 233) (d.stacks 212++d.stacks 216) ∈ nodes)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ProgramEncoding.encodeRecords` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.pairKey` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.Clean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.command` (definitions bundle `OAIQ081S091` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_present_from_rows` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourcePlanLookupFound.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.command_eval_found)

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

namespace Native
theorem command_eval_found (d : Data) (nodes : List (List Bool))
    (hmaster : d.stacks 337=ProgramEncoding.encodeRecords nodes) (hclean : Clean d) :
    ∃ n ≤ budget d nodes, ∃ e : Data,
      Eval command n d e ∧
      e.stacks=Function.update d.stacks 304
        (List.replicate (nodes.idxOf
          (pairKey (d.stacks 233) (d.stacks 212++d.stacks 216))) true) ∧
      e.regs 4=decide (pairKey (d.stacks 233) (d.stacks 212++d.stacks 216) ∈ nodes) := by
  sorry

end Native

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

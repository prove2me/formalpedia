-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHighContextProgram_Local_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.command_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:02:18.35097+00:00
-- url     : https://prove2.me/theorems/e3f17b30-4bba-4b6a-9f51-0ae1e6ab10c0
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHighContextProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHighContextProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.Subexp.BlockSearchPreparation`):
--
--   ```lean
--   theorem command_eval (regs : Fin 4 → Bool) (words : List (List Bool)) (mask : List Bool)
--       (hh : words.flatten.length = HighIncidenceProgram.Restriction.highCount mask) :
--       ∃ n rf, n ≤ cost words mask ∧ Eval command n
--         (state regs (ProgramEncoding.encodeRecords words) mask [] [] [] [] [] [] [] [])
--         (state rf (ProgramEncoding.encodeRecords words) mask mask.reverse
--           (HighIncidenceProgram.Restriction.zeroMerge mask words.flatten).reverse [] [] [] [] [] [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.zeroMerge` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ProgramEncoding.encodeRecords` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.cost` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.state` (definitions bundle `OAIQ081S126` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.command` (definitions bundle `OAIQ081S144` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace.prepare_high_space` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.prepare_high_resources` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHighContextProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.command_eval)

import Mathlib
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

theorem command_eval (regs : Fin 4 → Bool) (words : List (List Bool)) (mask : List Bool)
    (hh : words.flatten.length = HighIncidenceProgram.Restriction.highCount mask) :
    ∃ n rf, n ≤ cost words mask ∧ Eval command n
      (state regs (ProgramEncoding.encodeRecords words) mask [] [] [] [] [] [] [] [])
      (state rf (ProgramEncoding.encodeRecords words) mask mask.reverse
        (HighIncidenceProgram.Restriction.zeroMerge mask words.flatten).reverse [] [] [] [] [] []) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

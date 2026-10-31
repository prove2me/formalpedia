-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_EntryBank_covered_uncovered_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered_uncovered_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:03:58.713545+00:00
-- url     : https://prove2.me/theorems/60c0a31b-01a5-4067-b6a0-cb967e168b6f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered_uncovered_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered_uncovered_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankCovered.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankCovered.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes`, `open RowSelectionProgram`):
--
--   ```lean
--   theorem covered_uncovered_eval (a : Data) (h : MetadataReady a)
--       (hp : a.stacks 254=[]) (hn : a.stacks 255=[])
--       (h5 : a.regs 5=false) :
--       ∃ n ≤ 2*metadataFieldsLength a+601, ∃ rf,
--         Eval (.seq covered cleanup) n a (finish a rf ([],[]))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.cleanup` (definitions bundle `OAIQ081S123` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.Data` (definitions bundle `OAIQ081S142` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.MetadataReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.finish` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.metadataFieldsLength` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered` (definitions bundle `OAIQ081S174` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankCovered.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered_uncovered_eval)

import Mathlib
import Definitions.Def_OAIQ081S174

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open RowSelectionProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

theorem covered_uncovered_eval (a : Data) (h : MetadataReady a)
    (hp : a.stacks 254=[]) (hn : a.stacks 255=[])
    (h5 : a.regs 5=false) :
    ∃ n ≤ 2*metadataFieldsLength a+601, ∃ rf,
      Eval (.seq covered cleanup) n a (finish a rf ([],[])) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

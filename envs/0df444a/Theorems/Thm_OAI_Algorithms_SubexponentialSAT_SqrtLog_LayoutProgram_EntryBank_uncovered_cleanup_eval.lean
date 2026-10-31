-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_EntryBank_uncovered_cleanup_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.uncovered_cleanup_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:25:25.71304+00:00
-- url     : https://prove2.me/theorems/46f5b393-3ce4-4fc9-9f68-2517e8e99fcd
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.uncovered_cleanup_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.uncovered_cleanup_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankFrameUncovered.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankFrameUncovered.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp`):
--
--   ```lean
--   theorem uncovered_cleanup_eval (a : Data) (h : MetadataReady a)
--       (h254 : a.stacks 254=[]) :
--       ∃ n ≤ 27*((a.stacks 252).length+(a.stacks 253).length)+
--           2*metadataFieldsLength a+635,
--         ∃ z : Data, Eval (.seq uncovered cleanup) n a z ∧
--         (∀ j : Fin 256, z.stacks j=
--           if j.val < 200 then [] else if j=254 then
--             (if a.stacks 252=a.stacks 253 then [true] else []) else a.stacks j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.cleanup` (definitions bundle `OAIQ081S123` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.Data` (definitions bundle `OAIQ081S142` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.MetadataReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.metadataFieldsLength` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.uncovered` (definitions bundle `OAIQ081S156` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankFrameUncovered.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.uncovered_cleanup_eval)

import Mathlib
import Definitions.Def_OAIQ081S156

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem uncovered_cleanup_eval (a : Data) (h : MetadataReady a)
    (h254 : a.stacks 254=[]) :
    ∃ n ≤ 27*((a.stacks 252).length+(a.stacks 253).length)+
        2*metadataFieldsLength a+635,
      ∃ z : Data, Eval (.seq uncovered cleanup) n a z ∧
      (∀ j : Fin 256, z.stacks j=
        if j.val < 200 then [] else if j=254 then
          (if a.stacks 252=a.stacks 253 then [true] else []) else a.stacks j) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

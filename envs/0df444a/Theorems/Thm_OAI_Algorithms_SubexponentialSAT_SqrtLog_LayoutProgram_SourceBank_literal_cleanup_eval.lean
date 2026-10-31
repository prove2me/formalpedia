-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_literal_cleanup_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.literal_cleanup_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:43:30.02743+00:00
-- url     : https://prove2.me/theorems/86f56bcd-910f-4921-9172-85810df8a527
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.literal_cleanup_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.literal_cleanup_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrame.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrame.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp`):
--
--   ```lean
--   theorem literal_cleanup_eval (src : Fin 320) (hsrc : src=313 ∨ src=314) (a : Data)
--       (ht : a.stacks 319=[]) (h315 : a.stacks 315=[]) (h316 : a.stacks 316=[])
--       (h287 : a.stacks 287=[]) (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
--       ∃ n ≤ 14*(a.stacks src).length+19+120*B+180,
--         ∃ b : Data, Eval (.seq (literal src) cleanup) n a b ∧
--           b.stacks=Function.update (clearedStacks a) 287
--             (SubexponentialSAT.SubexpKernelControl.pushWord (a.stacks src))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.pushWord` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.cleanup` (definitions bundle `OAIQ081S124` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.literal` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Data` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.clearedStacks` (definitions bundle `OAIQ081S168` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.covered_uncovered_cleanup` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.uncovered_cleanup` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrame.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.literal_cleanup_eval)

import Mathlib
import Definitions.Def_OAIQ081S168

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem literal_cleanup_eval (src : Fin 320) (hsrc : src=313 ∨ src=314) (a : Data)
    (ht : a.stacks 319=[]) (h315 : a.stacks 315=[]) (h316 : a.stacks 316=[])
    (h287 : a.stacks 287=[]) (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∃ n ≤ 14*(a.stacks src).length+19+120*B+180,
      ∃ b : Data, Eval (.seq (literal src) cleanup) n a b ∧
        b.stacks=Function.update (clearedStacks a) 287
          (SubexponentialSAT.SubexpKernelControl.pushWord (a.stacks src)) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

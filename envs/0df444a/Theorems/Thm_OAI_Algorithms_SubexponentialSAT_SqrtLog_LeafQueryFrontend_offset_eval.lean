-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_offset_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.offset_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:30:46.973897+00:00
-- url     : https://prove2.me/theorems/c1383f0f-424b-4e11-bc6a-8adab1c0e3ba
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.offset_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.offset_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendFinish.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendFinish.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend`, with `open SubexponentialSAT BitProgram StructuredCalls`):
--
--   ```lean
--   theorem offset_eval (a : Data) (he : emptyRange a 650 668) (ho : a.stacks 141=[]) :
--       ∃ n ≤ LayoutOffsetProgram.budget (a.stacks 725) (a.stacks 720) (a.stacks 727), ∃ b,
--         Eval offsetCall n a b ∧
--         BinaryArithmetic.toNat (b.stacks 141)=2*BinaryArithmetic.toNat (a.stacks 725)*
--           (8*BinaryArithmetic.toNat (a.stacks 720))^(2*BinaryArithmetic.toNat (a.stacks 727)) ∧
--         (b.stacks 141).length ≤ LayoutOffsetProgram.outputLength (a.stacks 725) (a.stacks 720) (a.stacks 727) ∧
--         (∀ i : Fin 768, i≠141 → b.stacks i=a.stacks i) ∧ b.regs 8=a.regs 8
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.outputLength` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.emptyRange` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.offsetCall` (definitions bundle `OAIQ081S159` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval_uniform` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendFinish.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.offset_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S159

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem offset_eval (a : Data) (he : emptyRange a 650 668) (ho : a.stacks 141=[]) :
    ∃ n ≤ LayoutOffsetProgram.budget (a.stacks 725) (a.stacks 720) (a.stacks 727), ∃ b,
      Eval offsetCall n a b ∧
      BinaryArithmetic.toNat (b.stacks 141)=2*BinaryArithmetic.toNat (a.stacks 725)*
        (8*BinaryArithmetic.toNat (a.stacks 720))^(2*BinaryArithmetic.toNat (a.stacks 727)) ∧
      (b.stacks 141).length ≤ LayoutOffsetProgram.outputLength (a.stacks 725) (a.stacks 720) (a.stacks 727) ∧
      (∀ i : Fin 768, i≠141 → b.stacks i=a.stacks i) ∧ b.regs 8=a.regs 8 := by
  sorry

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_coreCommand_eval_bounded
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_bounded
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:25:17.27603+00:00
-- url     : https://prove2.me/theorems/fee3e211-31cd-44ff-bbbe-8ff2145a7085
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_bounded: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_bounded` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendCoreBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendCoreBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend`, with `open SubexponentialSAT BitProgram StructuredCalls`):
--
--   ```lean
--   theorem coreCommand_eval_bounded (q : Query) (k : ℕ) (a : Data) (hv : q.Valid) (hready : q.Ready a) :
--       ∃ n b tau l w, Eval (coreCommand k) n a b ∧
--         n ≤ coreBudget q k a tau l ∧
--         BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
--         b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
--         b.stacks 338=highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
--         b.stacks 719=q.forward ∧
--         projectState r9 bank b=LeafParametersProgram.Execute.state (b.regs ∘ r9) w ∧
--         LeafParametersProgram.Circuit.Shape (LeafParametersProgram.Execute.guardedModel (q.input k) l) w ∧
--         (b.regs 8=true ↔ LeafParametersProgram.Guard (q.input k)) ∧
--         (LeafParametersProgram.Guard (q.input k) → LeafParametersProgram.Layout.EncodesParameters
--           (LeafParametersProgram.produce (q.input k)) w) ∧
--         emptyRange b 648 680 ∧
--         (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) → i≠338 → i≠718 → i≠719 → b.stacks i=a.stacks i) ∧
--         tau.length ≤ Asymptotic.L (BinaryArithmetic.toNat q.ambient)+1 ∧
--         l=q.inputLengths k
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.L` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.bank` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.r9` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.threshold` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.produce` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highMask` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.scopeBits` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.state` (definitions bundle `OAIQ081S083` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.emptyRange` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Shape` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout.EncodesParameters` (definitions bundle `OAIQ081S109` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.forward` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.scopeRows` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Ready` (definitions bundle `OAIQ081S146` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.inputLengths` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand` (definitions bundle `OAIQ081S176` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreBudget` (definitions bundle `OAIQ081S183` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend_accepted_command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval_input_bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval_with_inputLengths` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendCoreBound.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_bounded)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S183

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

theorem coreCommand_eval_bounded (q : Query) (k : ℕ) (a : Data) (hv : q.Valid) (hready : q.Ready a) :
    ∃ n b tau l w, Eval (coreCommand k) n a b ∧
      n ≤ coreBudget q k a tau l ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧
      projectState r9 bank b=LeafParametersProgram.Execute.state (b.regs ∘ r9) w ∧
      LeafParametersProgram.Circuit.Shape (LeafParametersProgram.Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ LeafParametersProgram.Guard (q.input k)) ∧
      (LeafParametersProgram.Guard (q.input k) → LeafParametersProgram.Layout.EncodesParameters
        (LeafParametersProgram.produce (q.input k)) w) ∧
      emptyRange b 648 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) → i≠338 → i≠718 → i≠719 → b.stacks i=a.stacks i) ∧
      tau.length ≤ Asymptotic.L (BinaryArithmetic.toNat q.ambient)+1 ∧
      l=q.inputLengths k := by
  sorry

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

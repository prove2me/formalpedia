-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_postCommand_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:53:59.929684+00:00
-- url     : https://prove2.me/theorems/6a9065b1-8412-4e01-9ee6-95a7d309cf99
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendPost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendPost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend`, with `open SubexponentialSAT BitProgram StructuredCalls`, `open LeafParametersProgram`):
--
--   ```lean
--   theorem postCommand_eval (a : Data) (m : Circuit.Model) (w : Bank.Words)
--       (hs : Circuit.Shape m w)
--       (hp : projectState Exports.bankRegs Exports.bank a=Bank.state (a.regs ∘ Exports.bankRegs) w)
--       (hr : 0 < m.val 18) (hz : ∀ j,46 ≤ j.val → m.val j=0)
--       (ho : Exports.OutputEmpty a) (ht : emptyRange a 648 680)
--       (h134 : a.stacks 134=[]) (h141 : a.stacks 141=[])
--       (descending : List Bool) (h338 : a.stacks 338=descending) :
--       ∃ n b prepared beforeClean wf, Eval postCommand n a b ∧
--         n ≤ postBudget m prepared beforeClean descending ∧
--         Exported m b ∧
--         BinaryArithmetic.toNat (b.stacks 141)=2*m.val 3*(8*m.val 21)^(2*m.val 29) ∧
--         b.stacks 134=descending.reverse.map Bool.not ∧
--         projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) wf ∧
--         Circuit.Shape m wf ∧ b.regs 8=a.regs 8 ∧ emptyRange b 417 680 ∧
--         (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) → i≠134 → i≠141 →
--           (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.bank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.bankRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.destination` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.state` (definitions bundle `OAIQ081S083` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.OutputEmpty` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.emptyRange` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Shape` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Exported` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postBudget` (definitions bundle `OAIQ081S186` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval_with_inputLengths` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendPost.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186

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
open LeafParametersProgram

theorem postCommand_eval (a : Data) (m : Circuit.Model) (w : Bank.Words)
    (hs : Circuit.Shape m w)
    (hp : projectState Exports.bankRegs Exports.bank a=Bank.state (a.regs ∘ Exports.bankRegs) w)
    (hr : 0 < m.val 18) (hz : ∀ j,46 ≤ j.val → m.val j=0)
    (ho : Exports.OutputEmpty a) (ht : emptyRange a 648 680)
    (h134 : a.stacks 134=[]) (h141 : a.stacks 141=[])
    (descending : List Bool) (h338 : a.stacks 338=descending) :
    ∃ n b prepared beforeClean wf, Eval postCommand n a b ∧
      n ≤ postBudget m prepared beforeClean descending ∧
      Exported m b ∧
      BinaryArithmetic.toNat (b.stacks 141)=2*m.val 3*(8*m.val 21)^(2*m.val 29) ∧
      b.stacks 134=descending.reverse.map Bool.not ∧
      projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) wf ∧
      Circuit.Shape m wf ∧ b.regs 8=a.regs 8 ∧ emptyRange b 417 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) → i≠134 → i≠141 →
        (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks i) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

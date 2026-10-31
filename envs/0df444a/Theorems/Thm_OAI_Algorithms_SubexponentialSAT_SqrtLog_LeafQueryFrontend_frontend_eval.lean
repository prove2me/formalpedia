-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_frontend_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:51:32.660299+00:00
-- url     : https://prove2.me/theorems/5f1dfee0-244a-475b-b9b5-73fa2cca149c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend`, with `open SubexponentialSAT BitProgram StructuredCalls`, `open LeafParametersProgram`):
--
--   ```lean
--   theorem frontend_eval (q : Query) (k : ℕ) (a : Data) (hv : q.Valid)
--       (ha : q.Ready a) (ho : q.OutputEmpty a) :
--       ∃ n b counted prepared beforeClean tau l w,
--         Eval (frontend k) n a b ∧
--         n ≤ frontendBudget q k counted prepared beforeClean tau l ∧
--         BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
--         b.stacks 704=List.replicate q.rows.length true ∧
--         b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
--         b.stacks 338=highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
--         b.stacks 719=q.forward ∧ b.stacks 134=q.forward.map Bool.not ∧
--         Exported (Execute.guardedModel (q.input k) l) b ∧
--         BinaryArithmetic.toNat (b.stacks 141)=
--           2*(Execute.guardedModel (q.input k) l).val 3*
--           (8*(Execute.guardedModel (q.input k) l).val 21)^
--             (2*(Execute.guardedModel (q.input k) l).val 29) ∧
--         projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w ∧
--         Circuit.Shape (Execute.guardedModel (q.input k) l) w ∧
--         (b.regs 8=true ↔ Guard (q.input k)) ∧ emptyRange b 417 680 ∧
--         (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
--           i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 →
--           (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.bank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.bankRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.destination` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.threshold` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highMask` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.scopeBits` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.state` (definitions bundle `OAIQ081S083` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.emptyRange` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Shape` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.forward` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.scopeRows` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.OutputEmpty` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Ready` (definitions bundle `OAIQ081S146` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Exported` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend` (definitions bundle `OAIQ081S176` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontendBudget` (definitions bundle `OAIQ081S186` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.run` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval)

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

theorem frontend_eval (q : Query) (k : ℕ) (a : Data) (hv : q.Valid)
    (ha : q.Ready a) (ho : q.OutputEmpty a) :
    ∃ n b counted prepared beforeClean tau l w,
      Eval (frontend k) n a b ∧
      n ≤ frontendBudget q k counted prepared beforeClean tau l ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 704=List.replicate q.rows.length true ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧ b.stacks 134=q.forward.map Bool.not ∧
      Exported (Execute.guardedModel (q.input k) l) b ∧
      BinaryArithmetic.toNat (b.stacks 141)=
        2*(Execute.guardedModel (q.input k) l).val 3*
        (8*(Execute.guardedModel (q.input k) l).val 21)^
          (2*(Execute.guardedModel (q.input k) l).val 29) ∧
      projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w ∧
      Circuit.Shape (Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ Guard (q.input k)) ∧ emptyRange b 417 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
        i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 →
        (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks i) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

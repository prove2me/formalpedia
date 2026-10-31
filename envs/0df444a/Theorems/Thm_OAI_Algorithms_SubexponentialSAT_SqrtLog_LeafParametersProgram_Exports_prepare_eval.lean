-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_Exports_prepare_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepare_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:48:45.091725+00:00
-- url     : https://prove2.me/theorems/3f3793f6-4cf1-4737-94a4-256c72c0a894
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepare_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepare_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramExports.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramExports.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports`, with `open BitProgram StructuredCalls BinaryArithmetic Bank Circuit`):
--
--   ```lean
--   theorem prepare_eval (a : Data) (m : Model) (w : Words) (hs : Shape m w)
--       (hp : projectState bankRegs bank a=Bank.state (a.regs ∘ bankRegs) w)
--       (hr : 0 < m.val 18) (hz : ∀ j,46 ≤ j.val → m.val j=0)
--       (ho : OutputEmpty a) (ht : Scratch a) :
--       ∃ n ≤ prepareBudget m, ∃ rf wb,
--         Eval prepareCommand n a (cleared (exportState (cached a rf wb))) ∧
--         Shape (Interval.finalModel m) wb ∧ Shape m (restoredWords wb)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Regs` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.bank` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.bankRegs` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.state` (definitions bundle `OAIQ081S083` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.OutputEmpty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.Scratch` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.exportState` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Shape` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cached`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cleared` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.restoredWords` (definitions bundle `OAIQ081S109` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepareCommand` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.finalModel` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepareBudget` (definitions bundle `OAIQ081S186` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval_uniform` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramExports.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepare_eval)

import Mathlib
import Definitions.Def_OAIQ081S186

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem prepare_eval (a : Data) (m : Model) (w : Words) (hs : Shape m w)
    (hp : projectState bankRegs bank a=Bank.state (a.regs ∘ bankRegs) w)
    (hr : 0 < m.val 18) (hz : ∀ j,46 ≤ j.val → m.val j=0)
    (ho : OutputEmpty a) (ht : Scratch a) :
    ∃ n ≤ prepareBudget m, ∃ rf wb,
      Eval prepareCommand n a (cleared (exportState (cached a rf wb))) ∧
      Shape (Interval.finalModel m) wb ∧ Shape m (restoredWords wb) := by
  sorry

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

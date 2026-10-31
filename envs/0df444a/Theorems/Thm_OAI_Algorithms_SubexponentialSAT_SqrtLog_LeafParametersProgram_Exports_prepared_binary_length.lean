-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_Exports_prepared_binary_length
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_binary_length
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:50:48.790457+00:00
-- url     : https://prove2.me/theorems/62213649-d5d1-4174-bba8-1d326684ab84
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_binary_length: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_binary_length` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramExports.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramExports.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports`, with `open BitProgram StructuredCalls BinaryArithmetic Bank Circuit`):
--
--   ```lean
--   theorem prepared_binary_length (a : Data) (r : Regs) (m : Model) (w : Words)
--       (hs : Shape (Interval.finalModel m) w) (ho : OutputEmpty a) (ht : Scratch a) (i : Fin 8) :
--       ((cleared (exportState (cached a r w))).stacks (destination (i.natAdd 8))).length ≤
--         m.len (binarySources i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Regs` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.binarySources` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.destination` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.OutputEmpty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.Scratch` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.exportState` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Shape` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cached` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cleared` (definitions bundle `OAIQ081S109` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.finalModel` (definitions bundle `OAIQ081S169` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval_uniform` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramExports.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_binary_length)

import Mathlib
import Definitions.Def_OAIQ081S169

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem prepared_binary_length (a : Data) (r : Regs) (m : Model) (w : Words)
    (hs : Shape (Interval.finalModel m) w) (ho : OutputEmpty a) (ht : Scratch a) (i : Fin 8) :
    ((cleared (exportState (cached a r w))).stacks (destination (i.natAdd 8))).length ≤
      m.len (binarySources i) := by
  sorry

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

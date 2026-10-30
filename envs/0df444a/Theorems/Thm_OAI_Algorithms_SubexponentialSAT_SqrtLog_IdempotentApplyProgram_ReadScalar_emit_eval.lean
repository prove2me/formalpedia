-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_ReadScalar_emit_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.emit_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:01:03.713833+00:00
-- url     : https://prove2.me/theorems/4a3f0983-bdb7-40c3-af44-0caa8e2e971e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.emit_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.emit_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramReadScalar.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramReadScalar.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar`, with `open BitProgram StructuredCalls`, `open HashCircuitProgram.Native`):
--
--   ```lean
--   theorem emit_eval (d : Machine) (destination : Fin 96)
--       (hdst : destination=61 ∨ destination=67) (shape coeff : List Bool)
--       (hshape : d.stacks 89=shape) (hcoeff : d.stacks 81=coeff)
--       (h90 : d.stacks 90=[]) (h91 : d.stacks 91=[])
--       (h92 : d.stacks 92=[]) (hout : d.stacks destination=[]) :
--       ∃ rf, Eval (emitConstant destination) (8*shape.length+7*coeff.length+31) d
--         ⟨rf,Function.update (Function.update (Function.update d.stacks 89 []) 81 [])
--           destination (constantBytes shape.length coeff)⟩
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.constantBytes` (definitions bundle `OAIQ081S070` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.emitConstant` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.Machine` (definitions bundle `OAIQ081S085` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.add_constant_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.loop_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramReadScalar.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.emit_eval)

import Mathlib
import Definitions.Def_OAIQ081S085

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar
open BitProgram StructuredCalls
open HashCircuitProgram.Native

theorem emit_eval (d : Machine) (destination : Fin 96)
    (hdst : destination=61 ∨ destination=67) (shape coeff : List Bool)
    (hshape : d.stacks 89=shape) (hcoeff : d.stacks 81=coeff)
    (h90 : d.stacks 90=[]) (h91 : d.stacks 91=[])
    (h92 : d.stacks 92=[]) (hout : d.stacks destination=[]) :
    ∃ rf, Eval (emitConstant destination) (8*shape.length+7*coeff.length+31) d
      ⟨rf,Function.update (Function.update (Function.update d.stacks 89 []) 81 [])
        destination (constantBytes shape.length coeff)⟩ := by
  sorry

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar

end OAI.Algorithms
end

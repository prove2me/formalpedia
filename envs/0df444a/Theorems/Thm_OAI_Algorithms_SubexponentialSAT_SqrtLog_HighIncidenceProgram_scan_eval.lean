-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HighIncidenceProgram_scan_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scan_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:29:24.939989+00:00
-- url     : https://prove2.me/theorems/496cdbf1-9d65-4392-ab80-3e270ec21207
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scan_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scan_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HighIncidenceProgramScan.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HighIncidenceProgramScan.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem scan_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ))
--       (n cut : ℕ) (mask : List Bool) :
--       ∃ time rf, time ≤ scanBudget scopes n cut ∧
--         Eval scan time (state regs scopes 0 cut mask (unary n))
--           (state rf scopes n cut (highPrefix scopes cut n ++ mask) [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.highPrefix` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.unary` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scanBudget` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scan` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.state` (definitions bundle `OAIQ081S119` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HighIncidenceProgramScan.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scan_eval)

import Mathlib
import Definitions.Def_OAIQ081S119

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
attribute [local irreducible] query count compare
  SubexpIncidenceSlotProgram.scopeBits Subexp.IncidencePlanSpec.degree

theorem scan_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (n cut : ℕ) (mask : List Bool) :
    ∃ time rf, time ≤ scanBudget scopes n cut ∧
      Eval scan time (state regs scopes 0 cut mask (unary n))
        (state rf scopes n cut (highPrefix scopes cut n ++ mask) []) := by
  sorry

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

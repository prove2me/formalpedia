-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_frontend_time_le
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_time_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:52:34.020212+00:00
-- url     : https://prove2.me/theorems/8aa5ab95-4a07-4e17-a06a-d1e85a797a38
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_time_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_time_le` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendUniform.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendUniform.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend`, with `open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram`):
--
--   ```lean
--   theorem frontend_time_le (q : Query) (k : ℕ) {a b : Data} {n : ℕ}
--       (hv : q.Valid) (ha : q.Ready a) (ho : q.OutputEmpty a)
--       (he : Eval (frontend k) n a b) : n ≤ q.inputBudget k
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Data` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.OutputEmpty` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Ready` (definitions bundle `OAIQ081S146` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend` (definitions bundle `OAIQ081S176` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.inputBudget` (definitions bundle `OAIQ081S186` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.front_state` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendUniform.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_time_le)

import Mathlib
import Definitions.Def_OAIQ081S186

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem frontend_time_le (q : Query) (k : ℕ) {a b : Data} {n : ℕ}
    (hv : q.Valid) (ha : q.Ready a) (ho : q.OutputEmpty a)
    (he : Eval (frontend k) n a b) : n ≤ q.inputBudget k := by
  sorry

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

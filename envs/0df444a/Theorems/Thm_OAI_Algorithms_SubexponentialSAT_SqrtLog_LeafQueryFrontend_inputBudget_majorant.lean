-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_inputBudget_majorant
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_majorant
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:52:52.2102+00:00
-- url     : https://prove2.me/theorems/e9e8f1f3-f4a9-4251-a258-9e1cdff64267
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_majorant: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_majorant` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendPolynomial.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendPolynomial.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend`, with `open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram LeafScopeInputBounds`, `open LeafParametersProgram.FrontendBounds`):
--
--   ```lean
--   theorem inputBudget_majorant (C d : ℕ)
--       (hp : ∀ (x : Input) (l : Fin 8 → ℕ) (S : ℕ), CountsBound x S → (∀ i,l i ≤ S) →
--         Execute.runtimeBound x l+Exports.prepareBudget (Execute.guardedModel x l)+
--           5000*(2*(Execute.guardedModel x l).val 29+1)^2*
--             ((Execute.guardedModel x l).len 3+(Execute.guardedModel x l).len 21+
--               (Execute.guardedModel x l).len 29+11)^2 ≤ C*(S+1)^d)
--       (q : Query) (k : ℕ) (hv : q.Valid) :
--       q.inputBudget k ≤ finalMajorant C d (capacity q k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Input` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.finalMajorant` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.capacity` (definitions bundle `OAIQ081S110` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.CountsBound` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.runtimeBound` (definitions bundle `OAIQ081S173` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepareBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.inputBudget` (definitions bundle `OAIQ081S186` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_polynomial` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendPolynomial.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_majorant)

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
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram LeafScopeInputBounds
open LeafParametersProgram.FrontendBounds
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem inputBudget_majorant (C d : ℕ)
    (hp : ∀ (x : Input) (l : Fin 8 → ℕ) (S : ℕ), CountsBound x S → (∀ i,l i ≤ S) →
      Execute.runtimeBound x l+Exports.prepareBudget (Execute.guardedModel x l)+
        5000*(2*(Execute.guardedModel x l).val 29+1)^2*
          ((Execute.guardedModel x l).len 3+(Execute.guardedModel x l).len 21+
            (Execute.guardedModel x l).len 29+11)^2 ≤ C*(S+1)^d)
    (q : Query) (k : ℕ) (hv : q.Valid) :
    q.inputBudget k ≤ finalMajorant C d (capacity q k) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

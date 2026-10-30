-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafScopeInputBounds_scope_cost_le
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.scope_cost_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:31:00.366715+00:00
-- url     : https://prove2.me/theorems/0541f5f8-f60a-4a24-8e60-f107102d39df
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.scope_cost_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.scope_cost_le` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafScopeInputBoundsQuery.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafScopeInputBoundsQuery.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds`, with `open LeafQueryFrontend`):
--
--   ```lean
--   theorem scope_cost_le (q : Query) (k : ℕ) (hv : q.Valid) :
--       HashScopeProgram.Complete.cost 1 0 q.width.length q.modulus q.clauses q.codes q.rows q.mark q.index ≤
--         HashScopeProgram.Complete.polynomialBound (capacity q k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.polynomialBound` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.capacity` (definitions bundle `OAIQ081S110` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.cost` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_majorant` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafScopeInputBoundsQuery.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.scope_cost_le)

import Mathlib
import Definitions.Def_OAIQ081S158

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafScopeInputBounds
open LeafQueryFrontend

theorem scope_cost_le (q : Query) (k : ℕ) (hv : q.Valid) :
    HashScopeProgram.Complete.cost 1 0 q.width.length q.modulus q.clauses q.codes q.rows q.mark q.index ≤
      HashScopeProgram.Complete.polynomialBound (capacity q k) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

end OAI.Algorithms
end

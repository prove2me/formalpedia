-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafScopeInputBounds_query_bounds
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.query_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:30:55.2312+00:00
-- url     : https://prove2.me/theorems/4078e287-7bfd-4e16-b7a9-f4d9a28fb253
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.query_bounds: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.query_bounds` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafScopeInputBoundsQuery.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafScopeInputBoundsQuery.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds`, with `open LeafQueryFrontend`):
--
--   ```lean
--   theorem query_bounds (q : Query) (k : ℕ) (hv : q.Valid) : QueryBounds q k
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.QueryBounds` (definitions bundle `OAIQ081S159` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.marked_with_shadow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_majorant` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.scope_cost_le` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafScopeInputBoundsQuery.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.query_bounds)

import Mathlib
import Definitions.Def_OAIQ081S158
import Definitions.Def_OAIQ081S159

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafScopeInputBounds
open LeafQueryFrontend

theorem query_bounds (q : Query) (k : ℕ) (hv : q.Valid) : QueryBounds q k := by
  sorry

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

end OAI.Algorithms
end

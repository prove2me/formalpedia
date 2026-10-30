-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafScopeInputBounds_statistics_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.statistics_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:43:28.926018+00:00
-- url     : https://prove2.me/theorems/f91248c9-9c7e-4c2d-8c55-45beb6029d75
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.statistics_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.statistics_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafScopeInputBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafScopeInputBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds`, with `open LeafStatisticsProgram LeafStatisticsSemantics`):
--
--   ```lean
--   theorem statistics_bound (scopes : List (List ℕ)) (mask : List Bool) (n S : ℕ)
--       (hS : 1 ≤ S) (hn : n ≤ S) (hm : mask.length ≤ S) (hc : scopes.length ≤ S)
--       (hd : ∀ row ∈ scopes, row.Nodup) (hi : ∀ row ∈ scopes, ∀ v ∈ row, v < n) :
--       StatisticsBound scopes mask S
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.StatisticsBound` (definitions bundle `OAIQ081S039` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.query_bounds` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafScopeInputBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.statistics_bound)

import Mathlib
import Definitions.Def_OAIQ081S039

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafScopeInputBounds
open LeafStatisticsProgram LeafStatisticsSemantics

theorem statistics_bound (scopes : List (List ℕ)) (mask : List Bool) (n S : ℕ)
    (hS : 1 ≤ S) (hn : n ≤ S) (hm : mask.length ≤ S) (hc : scopes.length ≤ S)
    (hd : ∀ row ∈ scopes, row.Nodup) (hi : ∀ row ∈ scopes, ∀ v ∈ row, v < n) :
    StatisticsBound scopes mask S := by
  sorry

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

end OAI.Algorithms
end

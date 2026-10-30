-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryStreamBudgets_high_loop_budget_polynomial
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets.high_loop_budget_polynomial
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:37:12.514073+00:00
-- url     : https://prove2.me/theorems/6d12d453-1d76-459c-aa73-9fb0d8778b20
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets.high_loop_budget_polynomial: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets.high_loop_budget_polynomial` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets`, with `open SqrtLog SubexpLiftRing SubexpQuarticRing`, `open CostAssembly.Polynomial QueryStreamCorrect`):
--
--   ```lean
--   theorem high_loop_budget_polynomial : ∃ C e : ℕ,
--       ∀ n t d Q J A S work U L H : ℕ,
--       n ≤ U → t ≤ U → d ≤ U → Q ≤ U → J ≤ U → A ≤ U → S ≤ U →
--       L ≤ U → H ≤ U →
--       2^H*(budget n t d Q J A S work+11*L+16*(n+2)+28*H+27)+3 ≤
--         C*(U+1)^e*(work+1)^2*2^H
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.budget` (definitions bundle `OAIQ081S183` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.runtime_bound` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets.high_loop_budget_polynomial)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S183

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
open SqrtLog SubexpLiftRing SubexpQuarticRing
open CostAssembly.Polynomial QueryStreamCorrect

theorem high_loop_budget_polynomial : ∃ C e : ℕ,
    ∀ n t d Q J A S work U L H : ℕ,
    n ≤ U → t ≤ U → d ≤ U → Q ≤ U → J ≤ U → A ≤ U → S ≤ U →
    L ≤ U → H ≤ U →
    2^H*(budget n t d Q J A S work+11*L+16*(n+2)+28*H+27)+3 ≤
      C*(U+1)^e*(work+1)^2*2^H := by
  sorry

open SqrtLog SqrtLog.Statement

open Filter SqrtLog SqrtLog.Statement

open SqrtLog SqrtLog.Statement

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
end

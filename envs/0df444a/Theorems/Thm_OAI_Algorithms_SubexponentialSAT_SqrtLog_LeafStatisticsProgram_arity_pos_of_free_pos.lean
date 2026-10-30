-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafStatisticsProgram_arity_pos_of_free_pos
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.arity_pos_of_free_pos
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T23:33:20.754746+00:00
-- url     : https://prove2.me/theorems/d2ba9358-95cc-4829-b35e-1a8f3698bc06
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.arity_pos_of_free_pos: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.arity_pos_of_free_pos` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafStatisticsProgramPositivity.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafStatisticsProgramPositivity.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram`, with `open scoped BigOperators`, `open LeafStatisticsSemantics`):
--
--   ```lean
--   theorem arity_pos_of_free_pos (scopes : List (List ℕ)) (mask : List Bool)
--       (hn : ∀ row ∈ scopes, row.Nodup)
--       (hfree : 0 < (measured scopes mask).free) :
--       0 < max (Arity.arity mask scopes 0)
--         (if (measured scopes mask).uncovered = 0 then 0 else 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.measured`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.arity` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Totals` (definitions bundle `OAIQ081S007` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_measured_guards` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafStatisticsProgramPositivity.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.arity_pos_of_free_pos)

import Mathlib
import Definitions.Def_OAIQ081S007

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open scoped BigOperators
open LeafStatisticsSemantics

theorem arity_pos_of_free_pos (scopes : List (List ℕ)) (mask : List Bool)
    (hn : ∀ row ∈ scopes, row.Nodup)
    (hfree : 0 < (measured scopes mask).free) :
    0 < max (Arity.arity mask scopes 0)
      (if (measured scopes mask).uncovered = 0 then 0 else 1) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

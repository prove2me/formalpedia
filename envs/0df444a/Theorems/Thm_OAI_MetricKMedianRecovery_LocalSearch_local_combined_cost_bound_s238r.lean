-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_LocalSearch_local_combined_cost_bound_s238r
-- name    : OAI.MetricKMedianRecovery.LocalSearch.local_combined_cost_bound_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:29:41.434083+00:00
-- url     : https://prove2.me/theorems/45b8e6a0-ca6c-4779-93cd-3e2f3217d022
-- title:
--   OAI.MetricKMedianRecovery.LocalSearch.local_combined_cost_bound_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.LocalSearch.local_combined_cost_bound` of [lean/OAI/Combinatorics/KMedianRecovery/Geometry/AllBadCostBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/AllBadCostBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.LocalSearch`):
--
--   ```lean
--   lemma local_combined_cost_bound_s238r (F D S O : Finset V) (hS : S.Nonempty) (hO : O.Nonempty)
--       (hSF : S ⊆ F) (hlocal : WidthLocalMin F D S 5) (hOF : O ⊆ F)
--       (hcard : O.card ≤ S.card) :
--       (∑ p ∈ D, (connection S p + connection O p)) ≤ 6*cost D O
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.LocalSearch.connection` (definitions bundle `Q238L000` of this split); `OAI.MetricKMedianRecovery.LocalSearch.WidthLocalMin` and `OAI.MetricKMedianRecovery.LocalSearch.cost` (definitions bundle `Q238L010` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.Anchoring.anchoring_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/AllBadCostBound.lean (declaration OAI.MetricKMedianRecovery.LocalSearch.local_combined_cost_bound)

import Mathlib
import Definitions.Def_Q238L010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma local_combined_cost_bound_s238r (F D S O : Finset V) (hS : S.Nonempty) (hO : O.Nonempty)
    (hSF : S ⊆ F) (hlocal : WidthLocalMin F D S 5) (hOF : O ⊆ F)
    (hcard : O.card ≤ S.card) :
    (∑ p ∈ D, (connection S p + connection O p)) ≤ 6*cost D O := by
  sorry

end MetricKMedianRecovery.LocalSearch

end OAI
end

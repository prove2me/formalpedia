-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_LocalSearch_local_five_approx_s238r
-- name    : OAI.MetricKMedianRecovery.LocalSearch.local_five_approx_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:29:45.330295+00:00
-- url     : https://prove2.me/theorems/ffbb12e2-b9ca-4c38-8a08-dc7c325a576c
-- title:
--   OAI.MetricKMedianRecovery.LocalSearch.local_five_approx_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.LocalSearch.local_five_approx` of [lean/OAI/Combinatorics/KMedianRecovery/Geometry/AllBadCostBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/AllBadCostBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.LocalSearch`):
--
--   ```lean
--   lemma local_five_approx_s238r (F D S O : Finset V) (hS : S.Nonempty) (hO : O.Nonempty)
--       (hSF : S ⊆ F) (hlocal : WidthLocalMin F D S 5) (hOF : O ⊆ F)
--       (hcard : O.card ≤ S.card) : cost D S ≤ 5*cost D O
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.LocalSearch.WidthLocalMin` and `OAI.MetricKMedianRecovery.LocalSearch.cost` (definitions bundle `Q238L010` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238r` and `OAI.MetricKMedianRecovery.LocalSearch.local_combined_cost_bound_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/AllBadCostBound.lean (declaration OAI.MetricKMedianRecovery.LocalSearch.local_five_approx)

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

lemma local_five_approx_s238r (F D S O : Finset V) (hS : S.Nonempty) (hO : O.Nonempty)
    (hSF : S ⊆ F) (hlocal : WidthLocalMin F D S 5) (hOF : O ⊆ F)
    (hcard : O.card ≤ S.card) : cost D S ≤ 5*cost D O := by
  sorry

end MetricKMedianRecovery.LocalSearch

end OAI
end

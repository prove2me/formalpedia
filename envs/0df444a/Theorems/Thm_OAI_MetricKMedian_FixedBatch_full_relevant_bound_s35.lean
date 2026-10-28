-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FixedBatch_full_relevant_bound_s35
-- name    : OAI.MetricKMedian.FixedBatch.full_relevant_bound_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:34:28.901981+00:00
-- url     : https://prove2.me/theorems/88d5670c-1326-4652-b5d7-490cbc67cde8
-- title:
--   OAI.MetricKMedian.FixedBatch.full_relevant_bound_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FixedBatch`, with `open Finset PhysicalPotential FiniteGraph`):
--
--   ```lean
--    theorem full_relevant_bound_s35 (G : I → Finset I) (S : Finset I) {Δ : ℕ}
--       (hS : S.card ≤ Δ) (hG : ∀ i, (G i).card=Δ) :
--       (relevant (graphActions G) S).card ≤ Δ^2+Δ
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FixedBatch.graphActions` and `OAI.MetricKMedian.FixedBatch.relevant` (definitions bundle `OAIQ035K004` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential FiniteGraph
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

 theorem full_relevant_bound_s35 (G : I → Finset I) (S : Finset I) {Δ : ℕ}
    (hS : S.card ≤ Δ) (hG : ∀ i, (G i).card=Δ) :
    (relevant (graphActions G) S).card ≤ Δ^2+Δ := by
  sorry

end MetricKMedian.FixedBatch
end
end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FixedBatch_count_action_size_s35
-- name    : OAI.MetricKMedian.FixedBatch.count_action_size_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:36:23.328985+00:00
-- url     : https://prove2.me/theorems/ad647082-10fc-4963-9b36-b16b82d35ea5
-- title:
--   OAI.MetricKMedian.FixedBatch.count_action_size_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FixedBatch`, with `open Finset PhysicalPotential`):
--
--   ```lean
--    theorem count_action_size_s35 (G : I → Finset I) (H : Finset I) {Δ : ℕ} {g B : ℝ}
--       (hg : 0 ≤ g) (hgB : g ≤ B) (hB : ∀ h, h ∉ H → mass g ((graphActions G).erase h) ≤ B)
--       (e : HeavyAction (graphActions G) H) :
--       countOpening (heavyActions (graphActions G) H) Δ e+
--         mass g (countErase (heavyActions (graphActions G) H) Δ e) ≤ B+2
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.graphActions`, `OAI.MetricKMedian.FixedBatch.heavyActions`, `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction` and `OAI.MetricKMedian.FixedBatch.Actions` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.FixedBatch.countErase` and `OAI.MetricKMedian.FixedBatch.countOpening` (definitions bundle `OAIQ035K021` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

 theorem count_action_size_s35 (G : I → Finset I) (H : Finset I) {Δ : ℕ} {g B : ℝ}
    (hg : 0 ≤ g) (hgB : g ≤ B) (hB : ∀ h, h ∉ H → mass g ((graphActions G).erase h) ≤ B)
    (e : HeavyAction (graphActions G) H) :
    countOpening (heavyActions (graphActions G) H) Δ e+
      mass g (countErase (heavyActions (graphActions G) H) Δ e) ≤ B+2 := by
  sorry

end MetricKMedian.FixedBatch
end
end

end OAI
end

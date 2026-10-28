-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FixedBatch_masked_mass_sum_s35
-- name    : OAI.MetricKMedian.FixedBatch.masked_mass_sum_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:36:53.048402+00:00
-- url     : https://prove2.me/theorems/aabb3d02-370f-46ce-9cab-a6e0b5fd175e
-- title:
--   OAI.MetricKMedian.FixedBatch.masked_mass_sum_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FixedBatch`, with `open Finset PhysicalPotential SourceBalance`):
--
--   ```lean
--    theorem masked_mass_sum_s35 (G : I → Finset I) (H : Finset I) (Δ : ℕ) {g : ℝ}
--       (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
--       (hH : ∀ h ∈ H, 1 < mass g ((graphActions G).erase h)) :
--       (∑ e, mass g (countErase (heavyActions (graphActions G) H) Δ e))=
--         ∑ h ∈ nonzero (fun h => mass g ((graphActions G).erase h)), mass g ((graphActions G).erase h)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.graphActions`, `OAI.MetricKMedian.FixedBatch.heavyActions`, `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction`, `OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction` and `OAI.MetricKMedian.FixedBatch.Actions` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.SourceBalance.nonzero` (definitions bundle `OAIQ035K011` of this split); `OAI.MetricKMedian.FixedBatch.countErase` (definitions bundle `OAIQ035K021` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.FixedBatch.masked_total_bound_s35` and `OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s35` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K011
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
open Finset PhysicalPotential SourceBalance
variable {I : Type*} [Fintype I] [DecidableEq I]

 theorem masked_mass_sum_s35 (G : I → Finset I) (H : Finset I) (Δ : ℕ) {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (hH : ∀ h ∈ H, 1 < mass g ((graphActions G).erase h)) :
    (∑ e, mass g (countErase (heavyActions (graphActions G) H) Δ e))=
      ∑ h ∈ nonzero (fun h => mass g ((graphActions G).erase h)), mass g ((graphActions G).erase h) := by
  sorry

end MetricKMedian.FixedBatch
end
end

end OAI
end

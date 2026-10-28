-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FixedBatch_heavy_charge_le_s35
-- name    : OAI.MetricKMedian.FixedBatch.heavy_charge_le_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:36:24.704393+00:00
-- url     : https://prove2.me/theorems/727f8e8e-24d1-4f67-a074-5bc51a7bff13
-- title:
--   OAI.MetricKMedian.FixedBatch.heavy_charge_le_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FixedBatch`, with `open Finset PhysicalPotential`):
--
--   ```lean
--   theorem heavy_charge_le_s35 (G : I → Finset I) (H S : Finset I)
--       (hHS : Disjoint H S) (x g b : ℝ) (d : I → ℝ)
--       (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i) :
--       (∑ e ∈ relevant (heavyActions (graphActions G) H) S,
--         charge (heavyActions (graphActions G) H) x g b d S e) ≤
--       ∑ h ∈ relevant (graphActions G) S, charge (graphActions G) x g b d S h
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.graphActions`, `OAI.MetricKMedian.FixedBatch.heavyActions`, `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction`, `OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction` and `OAI.MetricKMedian.FixedBatch.relevant` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.FixedBatch.charge` (definitions bundle `OAIQ035K021` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s35` of this split imports it.
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
variable {I : Type*} [DecidableEq I] [Fintype I]

theorem heavy_charge_le_s35 (G : I → Finset I) (H S : Finset I)
    (hHS : Disjoint H S) (x g b : ℝ) (d : I → ℝ)
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i) :
    (∑ e ∈ relevant (heavyActions (graphActions G) H) S,
      charge (heavyActions (graphActions G) H) x g b d S e) ≤
    ∑ h ∈ relevant (graphActions G) S, charge (graphActions G) x g b d S h := by
  sorry

end MetricKMedian.FixedBatch
end
end

end OAI
end

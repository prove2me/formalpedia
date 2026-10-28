-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FixedBatch_ideal_local_lower_s35
-- name    : OAI.MetricKMedian.FixedBatch.ideal_local_lower_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:36:25.20343+00:00
-- url     : https://prove2.me/theorems/d5416eaa-c526-4a73-9f76-9b52c98c9359
-- title:
--   OAI.MetricKMedian.FixedBatch.ideal_local_lower_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FixedBatch`, with `open Finset PhysicalPotential Analytic`):
--
--   ```lean
--   theorem ideal_local_lower_s35 (D : Actions I E) {x g b Q : ℝ}
--       (d : I → ℝ) (S : Finset I)
--       (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 < g) (hQ : 0 ≤ Q)
--       (hd0 : ∀ i, 0 ≤ d i) (hdQ : ∀ i ∈ S, d i ≤ Q/g)
--       (hy : mass g S ≤ 1) (hVQ : PhysicalPotential.cost g d S ≤ Q)
--       (hb0 : 0 ≤ b) (hbQ : b ≤ 5*(Q/g)) :
--       -(8*((relevant D S).card:ℝ)+2)*Q ≤
--         timeRate x (mass g S)*PhysicalPotential.cost g d S+
--           g*(∑ e ∈ relevant D S, charge D x g b d S e)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.timeRate` (definitions bundle `OAIQ035K000` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FixedBatch.Actions` and `OAI.MetricKMedian.FixedBatch.relevant` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.PhysicalPotential.cost` (definitions bundle `OAIQ035K007` of this split); `OAI.MetricKMedian.FixedBatch.charge` (definitions bundle `OAIQ035K021` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FixedBatch.forced_step_local_bound_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K021

section

attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

theorem ideal_local_lower_s35 (D : Actions I E) {x g b Q : ℝ}
    (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 < g) (hQ : 0 ≤ Q)
    (hd0 : ∀ i, 0 ≤ d i) (hdQ : ∀ i ∈ S, d i ≤ Q/g)
    (hy : mass g S ≤ 1) (hVQ : PhysicalPotential.cost g d S ≤ Q)
    (hb0 : 0 ≤ b) (hbQ : b ≤ 5*(Q/g)) :
    -(8*((relevant D S).card:ℝ)+2)*Q ≤
      timeRate x (mass g S)*PhysicalPotential.cost g d S+
        g*(∑ e ∈ relevant D S, charge D x g b d S e) := by
  sorry

end MetricKMedian.FixedBatch
end
end

end OAI
end

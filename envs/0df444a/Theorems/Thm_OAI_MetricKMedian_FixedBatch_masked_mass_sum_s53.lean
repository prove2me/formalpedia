-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FixedBatch_masked_mass_sum_s53
-- name    : OAI.MetricKMedian.FixedBatch.masked_mass_sum_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:34:48.066991+00:00
-- url     : https://prove2.me/theorems/fc5e6409-a70c-4ff9-b5e6-3808498536ab
-- title:
--   OAI.MetricKMedian.FixedBatch.masked_mass_sum_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.FixedBatch.masked_mass_sum` of [lean/OAI/Combinatorics/KMedian/Process/CountSource.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/CountSource.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FixedBatch`, with `open Finset PhysicalPotential SourceBalance`):
--
--   ```lean
--    theorem masked_mass_sum_s53 (G : I → Finset I) (H : Finset I) (Δ : ℕ) {g : ℝ}
--       (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
--       (hH : ∀ h ∈ H, 1 < mass g ((graphActions G).erase h)) :
--       (∑ e, mass g (countErase (heavyActions (graphActions G) H) Δ e))=
--         ∑ h ∈ nonzero (fun h => mass g ((graphActions G).erase h)), mass g ((graphActions G).erase h)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction`, `OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction` and `OAI.MetricKMedian.FixedBatch.Actions` (definitions bundle `OAIQ053K004` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.SourceBalance.nonzero` (definitions bundle `OAIQ053K012` of this split); `OAI.MetricKMedian.FixedBatch.graphActions` and `OAI.MetricKMedian.FixedBatch.heavyActions` (definitions bundle `OAIQ053K018` of this split); `OAI.MetricKMedian.FixedBatch.countErase` (definitions bundle `OAIQ053K020` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.FixedBatch.masked_total_bound_s53` and `OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s53` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/CountSource.lean (declaration OAI.MetricKMedian.FixedBatch.masked_mass_sum)

import Mathlib
import Definitions.Def_OAIQ053K012
import Definitions.Def_OAIQ053K018
import Definitions.Def_OAIQ053K020

section

attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

 theorem masked_mass_sum_s53 (G : I → Finset I) (H : Finset I) (Δ : ℕ) {g : ℝ}
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

-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseFixedCount_actual_count_tail_s35
-- name    : OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:47:48.106251+00:00
-- url     : https://prove2.me/theorems/234efa12-f44e-4f71-bf28-442da5faf753
-- title:
--   OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseFixedCount`, with `open Finset PhysicalPotential SourceBalance CountGeometry CountStatistic FixedBatch`):
--
--   ```lean
--   theorem actual_count_tail_s35 (G : I → Finset I) {Δ n : ℕ} {g : ℚ} {p φ b : ℝ}
--       (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < p) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
--       (hb : 0 < b) (hunit : (g:ℝ)*(Δ:ℝ)=1) (hG : ∀ i, (G i).card=Δ)
--       (hsmall : 8*p*(Δ:ℝ) ≤ φ*(g:ℝ))
--       (hlarge : 1 < b*amount (fun h => mass (g:ℝ) ((graphActions G).erase h))) :
--       let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
--       let H := univ.filter (fun h => max 1 (b*amount m) < m h)
--       let D := heavyActions (graphActions G) H
--       ∀ (enum : Fin n ≃ HeavyAction (graphActions G) H)
--         (q : HeavyAction (graphActions G) H → ℚ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1),
--       (∀ e, (q e:ℝ)=bias m p φ (heavyParent (graphActions G) H e)) →
--       (SparseEnumeratedBernoulli.law enum q hq).real.prob (fun ω => 0 < statistic
--         (fun e => countOpening D Δ e-mass (g:ℝ) (countErase D Δ e))
--         (fun e f => (g:ℝ)*(overlap (countErase D Δ) e f:ℝ)) ω) ≤
--         96*(Δ:ℝ)^2*b/(p*φ^2*(g:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.CountGeometry.overlap`, `OAI.MetricKMedian.CountStatistic.statistic`, `OAI.MetricKMedian.FiniteLaw.prob`, `OAI.MetricKMedian.FixedBatch.Actions`, `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.graphActions`, `OAI.MetricKMedian.FixedBatch.heavyActions`, `OAI.MetricKMedian.FixedBatch.heavyParent`, `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction` and `OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.SourceBalance.amount` and `OAI.MetricKMedian.SourceBalance.bias` (definitions bundle `OAIQ035K011` of this split); `OAI.MetricKMedian.FixedBatch.countErase` and `OAI.MetricKMedian.FixedBatch.countOpening` (definitions bundle `OAIQ035K021` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.SparseEnumeratedBernoulli.law` (definitions bundle `OAIQ035K049` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseCopyState.physical_count_tail_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K049

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseFixedCount
open Finset PhysicalPotential SourceBalance CountGeometry CountStatistic FixedBatch
variable {I : Type} [Fintype I] [DecidableEq I]

theorem actual_count_tail_s35 (G : I → Finset I) {Δ n : ℕ} {g : ℚ} {p φ b : ℝ}
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < p) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hb : 0 < b) (hunit : (g:ℝ)*(Δ:ℝ)=1) (hG : ∀ i, (G i).card=Δ)
    (hsmall : 8*p*(Δ:ℝ) ≤ φ*(g:ℝ))
    (hlarge : 1 < b*amount (fun h => mass (g:ℝ) ((graphActions G).erase h))) :
    let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
    let H := univ.filter (fun h => max 1 (b*amount m) < m h)
    let D := heavyActions (graphActions G) H
    ∀ (enum : Fin n ≃ HeavyAction (graphActions G) H)
      (q : HeavyAction (graphActions G) H → ℚ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1),
    (∀ e, (q e:ℝ)=bias m p φ (heavyParent (graphActions G) H e)) →
    (SparseEnumeratedBernoulli.law enum q hq).real.prob (fun ω => 0 < statistic
      (fun e => countOpening D Δ e-mass (g:ℝ) (countErase D Δ e))
      (fun e f => (g:ℝ)*(overlap (countErase D Δ) e f:ℝ)) ω) ≤
      96*(Δ:ℝ)^2*b/(p*φ^2*(g:ℝ)) := by
  sorry

end MetricKMedian.SparseFixedCount
end
end

end OAI
end

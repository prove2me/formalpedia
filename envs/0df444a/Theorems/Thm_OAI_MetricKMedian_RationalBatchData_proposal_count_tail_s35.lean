-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalBatchData_proposal_count_tail_s35
-- name    : OAI.MetricKMedian.RationalBatchData.proposal_count_tail_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:41:24.157369+00:00
-- url     : https://prove2.me/theorems/90478569-09eb-4420-a2a2-c22fe2a60379
-- title:
--   OAI.MetricKMedian.RationalBatchData.proposal_count_tail_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalBatchData`, with `open Finset FixedBatch PhysicalPotential`):
--
--   ```lean
--   theorem proposal_count_tail_s35 (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
--       (g β p φ : ℚ) (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
--       (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) β))
--       (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
--       (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
--       (hunit : (g:ℝ)*(Δ:ℝ)=1) (hG : ∀ i, (G i).card=Δ)
--       (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
--       (proposal G Δ g β p φ hp0 hφ0 hupper enum).real.prob
--         (fun Z => mass (g:ℝ) A+4/((g:ℝ)*(β:ℝ)) <
--           mass (g:ℝ) (transition A G (heavySet (graphMass G g) β) Z)) ≤
--         96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FiniteLaw.prob`, `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction` and `OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.RationalBatchData.heavySet` (definitions bundle `OAIQ035K005` of this split); `OAI.MetricKMedian.RationalBatchData.graph` and `OAI.MetricKMedian.RationalBatchData.graphMass` (definitions bundle `OAIQ035K017` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.RationalBatchData.proposal` (definitions bundle `OAIQ035K039` of this split); `OAI.MetricKMedian.RationalBatchData.transition` (definitions bundle `OAIQ035K040` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K039
import Definitions.Def_OAIQ035K040

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {F : Type} [DecidableEq F] {Δ n : ℕ}

theorem proposal_count_tail_s35 (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (g β p φ : ℚ) (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) β))
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
    (hunit : (g:ℝ)*(Δ:ℝ)=1) (hG : ∀ i, (G i).card=Δ)
    (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
    (proposal G Δ g β p φ hp0 hφ0 hupper enum).real.prob
      (fun Z => mass (g:ℝ) A+4/((g:ℝ)*(β:ℝ)) <
        mass (g:ℝ) (transition A G (heavySet (graphMass G g) β) Z)) ≤
      96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ)) := by
  sorry

end MetricKMedian.RationalBatchData
end
end

end OAI
end

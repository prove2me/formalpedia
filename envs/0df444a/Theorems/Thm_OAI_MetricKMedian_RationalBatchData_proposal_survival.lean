-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalBatchData_proposal_survival
-- name    : OAI.MetricKMedian.RationalBatchData.proposal_survival
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:30:11.417117+00:00
-- url     : https://prove2.me/theorems/11b3a549-6add-4700-b71c-e4c3e1a1d0b6
-- title:
--   OAI.MetricKMedian.RationalBatchData.proposal_survival: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalBatchData`, with `open Finset PhysicalPotential FixedBatch CopyState`):
--
--   ```lean
--   theorem proposal_survival (A S : Finset (Copy (F := F) Δ)) (G : A → Finset A)
--       (g β p φ : ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
--       (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) β))
--       {x h : ℝ} (d : F → ℝ) (hprob : (p:ℝ)=2*h*(g:ℝ))
--       (hG : ∀ i, (G i).card=Δ) (hg : 0 ≤ (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
--       (hh0 : 0 ≤ h) (hφ1 : (φ:ℝ) ≤ 1)
--       (hsmall : (2*h*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S ⊆ A) :
--       (proposal G Δ g β p φ hp hφ hupper enum).real.expect (fun Z =>
--         mass (g:ℝ) (roundAlive A S G (heavySet (graphMass G g) β) Z x (g:ℝ) d)) ≤
--         (1-h/2)*mass (g:ℝ) S
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FiniteLaw.expect`, `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction` and `OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.RationalBatchData.heavySet` (definitions bundle `OAIQ035K005` of this split); `OAI.MetricKMedian.RationalBatchData.graph` and `OAI.MetricKMedian.RationalBatchData.graphMass` (definitions bundle `OAIQ035K017` of this split); `OAI.MetricKMedian.CopyState.roundAlive` (definitions bundle `OAIQ035K028` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.RationalBatchData.proposal` (definitions bundle `OAIQ035K039` of this split).
--
--   **Used by.** The proofs of `OAI_MetricKMedian_RationalPhysicalKernel_histories_completed_expectation` and `OAI.MetricKMedian.RationalPhysicalKernel.step_survival` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K039

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset PhysicalPotential FixedBatch CopyState
variable {F : Type} [DecidableEq F] {Δ n : ℕ}

theorem proposal_survival (A S : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (g β p φ : ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) β))
    {x h : ℝ} (d : F → ℝ) (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hG : ∀ i, (G i).card=Δ) (hg : 0 ≤ (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hh0 : 0 ≤ h) (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (2*h*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S ⊆ A) :
    (proposal G Δ g β p φ hp hφ hupper enum).real.expect (fun Z =>
      mass (g:ℝ) (roundAlive A S G (heavySet (graphMass G g) β) Z x (g:ℝ) d)) ≤
      (1-h/2)*mass (g:ℝ) S := by
  sorry

end MetricKMedian.RationalBatchData
end
end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Completion_Rational_output_potential_s35
-- name    : OAI.MetricKMedian.Completion.Rational.output_potential_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:35:22.35826+00:00
-- url     : https://prove2.me/theorems/27b5a1bc-ccd8-4cf3-9e2e-f3fe0aa9f6eb
-- title:
--   OAI.MetricKMedian.Completion.Rational.output_potential_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Completion.Rational`, with `open Finset PhysicalPotential CopyState Analytic Preparation`):
--
--   ```lean
--   theorem output_potential_s35 (d : Fin j → F → ℚ) (R : Fin j → ℚ)
--       (location : F → X) (client : Fin j → X)
--       (hdist : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
--       (hR : ∀ c, 0 ≤ R c) {g x : ℝ} (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1)
--       (A : Finset (Copy (F := F) Δ)) (B L : Fin j → Finset (Copy (F := F) Δ))
--       (hB : ∀ c, (B c).Nonempty) (hm : ∀ c, mass g (B c)=1)
--       (hd : ∀ c i, i∈B c → d c i.1≤R c)
--       (hbackup : ∀ c, (¬∃ f∈integral Δ A, d c f ≤5*R c) → B c⊆A) :
--       (score d (output d R A B hB):ℝ) ≤ ∑ c, (
--         potential x g (fun i : Copy (F := F) Δ => dist (client c) (location i.1)) (L c)
--           (GroupCap.cap (R c:ℝ) (fun f => dist (client c) (location f)) (integral Δ A))+
--           5*(R c:ℝ)*mass g (L c))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Completion.Rational.score` (definitions bundle `OAIQ035K002` of this split); `OAI.MetricKMedian.CopyState.Copy`, `OAI.MetricKMedian.CopyState.integral`, `OAI.MetricKMedian.PhysicalPotential.mass` and `OAI.MetricKMedian.Completion.Rational.output` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.GroupCap.cap` (definitions bundle `OAIQ035K008` of this split); `OAI.MetricKMedian.PhysicalPotential.potential` (definitions bundle `OAIQ035K021` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalPhysicalKernel.histories_completion_s35` of this split imports it.
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
namespace MetricKMedian.Completion.Rational
open Finset PhysicalPotential CopyState Analytic Preparation
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j Δ : ℕ}

theorem output_potential_s35 (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (location : F → X) (client : Fin j → X)
    (hdist : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (hR : ∀ c, 0 ≤ R c) {g x : ℝ} (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1)
    (A : Finset (Copy (F := F) Δ)) (B L : Fin j → Finset (Copy (F := F) Δ))
    (hB : ∀ c, (B c).Nonempty) (hm : ∀ c, mass g (B c)=1)
    (hd : ∀ c i, i∈B c → d c i.1≤R c)
    (hbackup : ∀ c, (¬∃ f∈integral Δ A, d c f ≤5*R c) → B c⊆A) :
    (score d (output d R A B hB):ℝ) ≤ ∑ c, (
      potential x g (fun i : Copy (F := F) Δ => dist (client c) (location i.1)) (L c)
        (GroupCap.cap (R c:ℝ) (fun f => dist (client c) (location f)) (integral Δ A))+
        5*(R c:ℝ)*mass g (L c)) := by
  sorry

end MetricKMedian.Completion.Rational
end

end OAI
end

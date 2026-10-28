-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_step_survival_s35
-- name    : OAI.MetricKMedian.RationalPhysicalKernel.step_survival_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:47:25.087147+00:00
-- url     : https://prove2.me/theorems/7b7b89ac-f61e-404e-977b-fea9ece6c213
-- title:
--   OAI.MetricKMedian.RationalPhysicalKernel.step_survival_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalPhysicalKernel`, with `open Finset PhysicalPotential`):
--
--   ```lean
--   theorem step_survival_s35 (d₀ : F → F → ℚ) (location : F → X)
--       (hd : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
--       (g β p φ P : ℚ) (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
--       (s : State F Δ g β) (S : Finset (CopyState.Copy (F := F) Δ))
--       {x h : ℝ} (d : F → ℝ) (hprob : (p:ℝ)=2*h*(g:ℝ))
--       (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
--       (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
--       (hh0 : 0 ≤ h) (hφ1 : (φ:ℝ) ≤ 1)
--       (hA : 1 ≤ mass (g:ℝ) s.1)
--       (hsmall : (2*h*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S ⊆ s.1) :
--       (step d₀ g β p φ P hp0 hφ0 hupper s).expectation
--         (fun t => mass (g:ℝ) (labels g β x (fun (_ : Unit) => d) t (fun _ => S) ())) ≤
--         (1-h/2)*mass (g:ℝ) S
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.Payload` and `OAI.MetricKMedian.RationalPhysicalKernel.State` (definitions bundle `OAIQ035K017` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.labels` (definitions bundle `OAIQ035K044` of this split); `OAI.MetricKMedian.SparseIntegerLaw.expectation` (definitions bundle `OAIQ035K045` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.step` (definitions bundle `OAIQ035K047` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K047

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype F] in

theorem step_survival_s35 (d₀ : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ P : ℚ) (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) (S : Finset (CopyState.Copy (F := F) Δ))
    {x h : ℝ} (d : F → ℝ) (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hh0 : 0 ≤ h) (hφ1 : (φ:ℝ) ≤ 1)
    (hA : 1 ≤ mass (g:ℝ) s.1)
    (hsmall : (2*h*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S ⊆ s.1) :
    (step d₀ g β p φ P hp0 hφ0 hupper s).expectation
      (fun t => mass (g:ℝ) (labels g β x (fun (_ : Unit) => d) t (fun _ => S) ())) ≤
      (1-h/2)*mass (g:ℝ) S := by
  sorry

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

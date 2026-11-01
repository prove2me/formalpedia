-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_survival_s53
-- name    : OAI.MetricKMedian.RationalPhysicalKernel.histories_survival_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:41:59.954987+00:00
-- url     : https://prove2.me/theorems/a9fa6917-044b-4a43-9460-72d832d65165
-- title:
--   OAI.MetricKMedian.RationalPhysicalKernel.histories_survival_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival` of [lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalHistorySurvival.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalHistorySurvival.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalPhysicalKernel`, with `open Finset PhysicalPotential`):
--
--   ```lean
--   theorem histories_survival_s53 (d₀ : F → F → ℚ) (location : F → X)
--       (hd : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
--       (g β p φ : ℚ) (P : ℕ → ℚ)
--       (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
--       (A S₀ : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
--       (x : ℕ → ℝ) (d : F → ℝ) {h : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
--       (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
--       (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
--       (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
--       (hA : 1 ≤ mass (g:ℝ) A)
--       (hsmall : (2*h*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S₀ ⊆ A) :
--       (histories d₀ g β p φ P hp0 hφ0 hupper A T).expectation
--         (fun z => mass (g:ℝ) (replay g β x (fun (_ : Unit) => d) (fun _ => S₀) z ())) ≤
--         (1-h/2)^T*mass (g:ℝ) S₀
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.SparseHistories.History` (definitions bundle `OAIQ053K004` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.State` (definitions bundle `OAIQ053K016` of this split); `OAI.MetricKMedian.SparseIntegerLaw.expectation` (definitions bundle `OAIQ053K037` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.histories` (definitions bundle `OAIQ053K039` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.replay` (definitions bundle `OAIQ053K043` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalHistorySurvival.lean (declaration OAI.MetricKMedian.RationalPhysicalKernel.histories_survival)

import Mathlib
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K039
import Definitions.Def_OAIQ053K043

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
variable {F X : Type} [LinearOrder F] [PseudoMetricSpace X] {Δ : ℕ}

theorem histories_survival_s53 (d₀ : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A S₀ : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (x : ℕ → ℝ) (d : F → ℝ) {h : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
    (hA : 1 ≤ mass (g:ℝ) A)
    (hsmall : (2*h*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S₀ ⊆ A) :
    (histories d₀ g β p φ P hp0 hφ0 hupper A T).expectation
      (fun z => mass (g:ℝ) (replay g β x (fun (_ : Unit) => d) (fun _ => S₀) z ())) ≤
      (1-h/2)^T*mass (g:ℝ) S₀ := by
  sorry

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_drift_s53
-- name    : OAI.MetricKMedian.RationalPhysicalKernel.histories_drift_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:41:16.322409+00:00
-- url     : https://prove2.me/theorems/2cf07694-b667-4804-a287-1fe570268da8
-- title:
--   OAI.MetricKMedian.RationalPhysicalKernel.histories_drift_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift` of [lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalHistoryDrift.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalHistoryDrift.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalPhysicalKernel`, with `open Finset PhysicalPotential FixedBatch Analytic CopyState`):
--
--   ```lean
--   theorem histories_drift_s53 (d₀ : F → F → ℚ) (location : F → X) (client : X)
--       (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
--       (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
--       (A S₀ : Finset (Copy (F := F) Δ)) (T : ℕ)
--       {h R ζ : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
--       (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
--       (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
--       (hA : 1 ≤ mass (g:ℝ) A) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
--       (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction (g:ℝ))
--       (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4)
--       (he : ∀ t < T, |(P t:ℝ)-Analytic.P (Real.exp (-(t:ℝ)*h))| ≤ ζ)
--       (hactive : S₀ ⊆ A) (hm₀ : mass (g:ℝ) S₀=1)
--       (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, dist client (location i.1) ≤ R)
--       (hR : ∃ i ∈ S₀, R=dist client (location i.1)) :
--       (histories d₀ g β p φ P hp hφ hupper A T).expectation (fun z =>
--         potential (Real.exp (-(T:ℝ)*h)) (g:ℝ) (fun i => dist client (location i.1))
--           (replay g β (fun t => Real.exp (-(t:ℝ)*h))
--             (fun (_ : Unit) f => dist client (location f)) (fun _ => S₀) z ())
--           (GroupCap.cap R (fun f => dist client (location f)) (integral Δ z.1.1))) ≤
--         (1+2/Real.exp 1)*PhysicalPotential.cost (g:ℝ) (fun i => dist client (location i.1)) S₀+
--         (T:ℝ)*(h*((g:ℝ)+12*ζ)*PhysicalPotential.cost (g:ℝ) (fun i => dist client (location i.1)) S₀+
--           batchConstant Δ*h*((φ:ℝ)+h)*R)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.P` (definitions bundle `OAIQ053K000` of this split); `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.CopyState.integral` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.FixedBatch.batchConstant` (definitions bundle `OAIQ053K003` of this split); `OAI.MetricKMedian.SparseHistories.History` (definitions bundle `OAIQ053K004` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.GroupCap.cap` and `OAI.MetricKMedian.PhysicalPotential.cost` (definitions bundle `OAIQ053K007` of this split); `OAI.MetricKMedian.PhysicalPotential.savingsFraction` (definitions bundle `OAIQ053K015` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.Payload` and `OAI.MetricKMedian.RationalPhysicalKernel.State` (definitions bundle `OAIQ053K016` of this split); `OAI.MetricKMedian.PhysicalPotential.potential` (definitions bundle `OAIQ053K020` of this split); `OAI.MetricKMedian.SparseIntegerLaw.expectation` (definitions bundle `OAIQ053K037` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.histories` (definitions bundle `OAIQ053K039` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.replay` (definitions bundle `OAIQ053K043` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalHistoryDrift.lean (declaration OAI.MetricKMedian.RationalPhysicalKernel.histories_drift)

import Mathlib
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K039
import Definitions.Def_OAIQ053K043

section

attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential FixedBatch Analytic CopyState
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}

theorem histories_drift_s53 (d₀ : F → F → ℚ) (location : F → X) (client : X)
    (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A S₀ : Finset (Copy (F := F) Δ)) (T : ℕ)
    {h R ζ : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction (g:ℝ))
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4)
    (he : ∀ t < T, |(P t:ℝ)-Analytic.P (Real.exp (-(t:ℝ)*h))| ≤ ζ)
    (hactive : S₀ ⊆ A) (hm₀ : mass (g:ℝ) S₀=1)
    (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, dist client (location i.1) ≤ R)
    (hR : ∃ i ∈ S₀, R=dist client (location i.1)) :
    (histories d₀ g β p φ P hp hφ hupper A T).expectation (fun z =>
      potential (Real.exp (-(T:ℝ)*h)) (g:ℝ) (fun i => dist client (location i.1))
        (replay g β (fun t => Real.exp (-(t:ℝ)*h))
          (fun (_ : Unit) f => dist client (location f)) (fun _ => S₀) z ())
        (GroupCap.cap R (fun f => dist client (location f)) (integral Δ z.1.1))) ≤
      (1+2/Real.exp 1)*PhysicalPotential.cost (g:ℝ) (fun i => dist client (location i.1)) S₀+
      (T:ℝ)*(h*((g:ℝ)+12*ζ)*PhysicalPotential.cost (g:ℝ) (fun i => dist client (location i.1)) S₀+
        batchConstant Δ*h*((φ:ℝ)+h)*R) := by
  sorry

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

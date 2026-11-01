-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_step_drift_s53
-- name    : OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:42:22.288168+00:00
-- url     : https://prove2.me/theorems/ac9dd0c4-724e-42f7-a783-ce80d7fb9526
-- title:
--   OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.RationalPhysicalKernel.step_drift` of [lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalDrift.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalDrift.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalPhysicalKernel`, with `open Finset PhysicalPotential FixedBatch Analytic CopyState`):
--
--   ```lean
--   theorem step_drift_s53 (d₀ : F → F → ℚ) (location : F → X) (client : X)
--       (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
--       (g β p φ P : ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
--       (s : State F Δ g β) (S S₀ : Finset (Copy (F := F) Δ))
--       {x h R ζ : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
--       (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
--       (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) s.1)
--       (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
--       (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction (g:ℝ))
--       (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4) (he : |(P:ℝ)-Analytic.P x| ≤ ζ)
--       (hactive : S ⊆ s.1) (hS : S ⊆ S₀) (hm₀ : mass (g:ℝ) S₀=1)
--       (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, dist client (location i.1) ≤ R)
--       (hR : ∃ i ∈ S₀, R=dist client (location i.1)) :
--       (step d₀ g β p φ P hp hφ hupper s).expectation (fun t =>
--         potential (x*Real.exp (-h)) (g:ℝ) (fun i => dist client (location i.1))
--           (labels g β x (fun (_ : Unit) f => dist client (location f)) t (fun _ => S) ())
--           (GroupCap.cap R (fun f => dist client (location f)) (integral Δ t.1))) ≤
--         potential x (g:ℝ) (fun i => dist client (location i.1)) S
--           (GroupCap.cap R (fun f => dist client (location f)) (integral Δ s.1))+
--         h*((g:ℝ)+12*ζ)*PhysicalPotential.cost (g:ℝ) (fun i => dist client (location i.1)) S+
--         batchConstant Δ*h*((φ:ℝ)+h)*R
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.P` (definitions bundle `OAIQ053K000` of this split); `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.CopyState.integral` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.FixedBatch.batchConstant` (definitions bundle `OAIQ053K003` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.GroupCap.cap` and `OAI.MetricKMedian.PhysicalPotential.cost` (definitions bundle `OAIQ053K007` of this split); `OAI.MetricKMedian.PhysicalPotential.savingsFraction` (definitions bundle `OAIQ053K015` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.Payload` and `OAI.MetricKMedian.RationalPhysicalKernel.State` (definitions bundle `OAIQ053K016` of this split); `OAI.MetricKMedian.PhysicalPotential.potential` (definitions bundle `OAIQ053K020` of this split); `OAI.MetricKMedian.SparseIntegerLaw.expectation` (definitions bundle `OAIQ053K037` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.step` (definitions bundle `OAIQ053K039` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.labels` (definitions bundle `OAIQ053K043` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalDrift.lean (declaration OAI.MetricKMedian.RationalPhysicalKernel.step_drift)

import Mathlib
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K039
import Definitions.Def_OAIQ053K043

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.rationalPhysicalDriftCopyOrder
theorem step_drift_s53 (d₀ : F → F → ℚ) (location : F → X) (client : X)
    (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ P : ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) (S S₀ : Finset (Copy (F := F) Δ))
    {x h R ζ : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) s.1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction (g:ℝ))
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4) (he : |(P:ℝ)-Analytic.P x| ≤ ζ)
    (hactive : S ⊆ s.1) (hS : S ⊆ S₀) (hm₀ : mass (g:ℝ) S₀=1)
    (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, dist client (location i.1) ≤ R)
    (hR : ∃ i ∈ S₀, R=dist client (location i.1)) :
    (step d₀ g β p φ P hp hφ hupper s).expectation (fun t =>
      potential (x*Real.exp (-h)) (g:ℝ) (fun i => dist client (location i.1))
        (labels g β x (fun (_ : Unit) f => dist client (location f)) t (fun _ => S) ())
        (GroupCap.cap R (fun f => dist client (location f)) (integral Δ t.1))) ≤
      potential x (g:ℝ) (fun i => dist client (location i.1)) S
        (GroupCap.cap R (fun f => dist client (location f)) (integral Δ s.1))+
      h*((g:ℝ)+12*ζ)*PhysicalPotential.cost (g:ℝ) (fun i => dist client (location i.1)) S+
      batchConstant Δ*h*((φ:ℝ)+h)*R := by
  sorry

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

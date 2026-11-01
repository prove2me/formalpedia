-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_step_count_tail_s53
-- name    : OAI.MetricKMedian.RationalPhysicalKernel.step_count_tail_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:42:29.50877+00:00
-- url     : https://prove2.me/theorems/108d4412-5fc7-4324-b56f-31a422d7dece
-- title:
--   OAI.MetricKMedian.RationalPhysicalKernel.step_count_tail_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.RationalPhysicalKernel.step_count_tail` of [lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalCount.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalCount.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalPhysicalKernel`, with `open Finset PhysicalPotential`):
--
--   ```lean
--   theorem step_count_tail_s53 (d : F → F → ℚ) (location : F → X)
--       (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
--       (g β p φ P : ℚ) (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
--       (s : State F Δ g β)
--       (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
--       (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
--       (hunit : (g:ℝ)*(Δ:ℝ)=1) (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
--       (hA : 1 ≤ mass (g:ℝ) s.1) (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
--       (step d g β p φ P hp0 hφ0 hupper s).expectation
--         (fun t => if mass (g:ℝ) s.1+4/((g:ℝ)*(β:ℝ)) < mass (g:ℝ) t.1 then 1 else 0) ≤
--         96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.Payload` and `OAI.MetricKMedian.RationalPhysicalKernel.State` (definitions bundle `OAIQ053K016` of this split); `OAI.MetricKMedian.SparseIntegerLaw.expectation` (definitions bundle `OAIQ053K037` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.step` (definitions bundle `OAIQ053K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalCount.lean (declaration OAI.MetricKMedian.RationalPhysicalKernel.step_count_tail)

import Mathlib
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K039

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.rationalPhysicalCountCopyOrder
omit [Fintype F] in

theorem step_count_tail_s53 (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g β p φ P : ℚ) (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β)
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
    (hunit : (g:ℝ)*(Δ:ℝ)=1) (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hA : 1 ≤ mass (g:ℝ) s.1) (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
    (step d g β p φ P hp0 hφ0 hupper s).expectation
      (fun t => if mass (g:ℝ) s.1+4/((g:ℝ)*(β:ℝ)) < mass (g:ℝ) t.1 then 1 else 0) ≤
      96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ)) := by
  sorry

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

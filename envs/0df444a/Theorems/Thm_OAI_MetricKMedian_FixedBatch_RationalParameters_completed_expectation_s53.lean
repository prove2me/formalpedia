-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FixedBatch_RationalParameters_completed_expectation_s53
-- name    : OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:38:38.328847+00:00
-- url     : https://prove2.me/theorems/c25accce-0960-4a04-894e-113da5850f6b
-- title:
--   OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation` of [lean/OAI/Combinatorics/KMedian/Geometry/RationalParameterizedHistory.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Geometry/RationalParameterizedHistory.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FixedBatch.RationalParameters`, with `open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational`):
--
--   ```lean
--   theorem completed_expectation_s53 (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
--       (location : F → X) (client : Fin j → X)
--       (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
--       (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
--       (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
--       (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty)
--       (hA : 1 ≤ mass (q.g:ℝ) A) (hBA : ∀ c, B c ⊆ A)
--       (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (q.g:ℝ) (B c)=1)
--       (hdR : ∀ c i, i∈B c → d c i.1 ≤ R c) (hatt : ∀ c, ∃ i∈B c, R c=d c i.1) :
--       (q.tree d₀ A).expectation (fun z => (score d (completed d R B hB q.g q.β z):ℝ)) ≤
--         (1+2/Real.exp 1+τ)*(∑ c, PhysicalPotential.cost (q.g:ℝ)
--           (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.Completion.Rational.score` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.SparseHistories.History` (definitions bundle `OAIQ053K004` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.PhysicalPotential.cost` (definitions bundle `OAIQ053K007` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters` (definitions bundle `OAIQ053K015` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.State` (definitions bundle `OAIQ053K016` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.completed` (definitions bundle `OAIQ053K030` of this split); `OAI.MetricKMedian.SparseIntegerLaw.expectation` (definitions bundle `OAIQ053K037` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters.tree` (definitions bundle `OAIQ053K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Geometry/RationalParameterizedHistory.lean (declaration OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation)

import Mathlib
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K039

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)

variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j : ℕ}

local instance rationalParameterizedHistoryCopyOrder_r1058b7_1 : LinearOrder (Copy (F := F) q.Δ) := copyOrder
theorem completed_expectation_s53 (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
    (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty)
    (hA : 1 ≤ mass (q.g:ℝ) A) (hBA : ∀ c, B c ⊆ A)
    (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (q.g:ℝ) (B c)=1)
    (hdR : ∀ c i, i∈B c → d c i.1 ≤ R c) (hatt : ∀ c, ∃ i∈B c, R c=d c i.1) :
    (q.tree d₀ A).expectation (fun z => (score d (completed d R B hB q.g q.β z):ℝ)) ≤
      (1+2/Real.exp 1+τ)*(∑ c, PhysicalPotential.cost (q.g:ℝ)
        (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c)) := by
  sorry

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

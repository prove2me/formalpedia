-- Prove2me | Theorems.Thm_OAI_Falconer_Regularization_nonendpoint_one_scale_gain
-- name    : OAI.Falconer.Regularization.nonendpoint_one_scale_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:43:46.62799+00:00
-- url     : https://prove2.me/theorems/0a9f7137-ff62-4e22-ad86-72a9a0f886e9
-- title:
--   OAI.Falconer.Regularization.nonendpoint_one_scale_gain: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.Regularization.nonendpoint_one_scale_gain` of [lean/OAI/MeasureTheory/Falconer/Estimates/NonendpointOneScale.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/NonendpointOneScale.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer.Regularization`, with `open Set MeasureTheory NormedSpace`, `open scoped ENNReal`):
--
--   ```lean
--   theorem nonendpoint_one_scale_gain (hpublished : PublishedPlanarFurstenberg)
--       {h : ℕ} {α t q C D s : ℝ}
--       (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t)
--       (ht : t-(h:ℝ) < 1) (htα : t < α) (hC : 0 ≤ C)
--       (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
--       (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s) :
--       ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
--         ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
--           μ Q.carrierᶜ = 0 →
--           (∀ y : Space (h+2), ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
--         ∀ A P : Set (Space (h+2)), MeasurableSet A → MeasurableSet P →
--           μ Aᶜ = 0 → ν Pᶜ = 0 →
--           (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
--           (∀ y ∈ Q.carrier, ∀ x ∈ P, ‖y-x‖ ≤ D) →
--         ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
--           (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
--             ∀ u : Space (h+2), ‖u‖ = 1 →
--               ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
--                 ENNReal.ofReal (((2:ℝ)^N)^ε*r^q)) →
--         ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
--           (μ.prod ν) (G \ G') ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
--           ∀ x u : Space (h+2), μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
--             ENNReal.ofReal (((2:ℝ)^N)^(-q-c))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.DyadicCube`, `OAI.Falconer.Space` and `OAI.Falconer.DyadicCube.carrier` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedPlanarFurstenberg` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.TwoProjectionPieces.odd_original_caps_partition` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/NonendpointOneScale.lean (declaration OAI.Falconer.Regularization.nonendpoint_one_scale_gain)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_one_scale_gain (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {α t q C D s : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t)
    (ht : t-(h:ℝ) < 1) (htα : t < α) (hC : 0 ≤ C)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 →
        (∀ y : Space (h+2), ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space (h+2)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^q)) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ x u : Space (h+2), μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-q-c)) := by
  sorry

end Falconer.Regularization

end OAI
end

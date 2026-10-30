-- Prove2me | Theorems.Thm_OAI_Falconer_endpoint_original_middle_pruning
-- name    : OAI.Falconer.endpoint_original_middle_pruning
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:48:49.421741+00:00
-- url     : https://prove2.me/theorems/7d7d83ce-e4c0-4d9a-9228-e1aeffd031ee
-- title:
--   OAI.Falconer.endpoint_original_middle_pruning: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.endpoint_original_middle_pruning` of [lean/OAI/MeasureTheory/Falconer/Estimates/EndpointOriginalMiddle.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/EndpointOriginalMiddle.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory NormedSpace`, `open scoped ENNReal`):
--
--   ```lean
--   theorem endpoint_original_middle_pruning (hLW : PublishedFiniteLoomisWhitney)
--       {h : ℕ} {t ζ : ℝ} (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
--       (hζ : 0 < ζ) :
--       ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
--         ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+3)))
--           [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
--         ∀ (_w₀ : Sphere (h+3)) (c : Space (h+3)) (a : ℝ), 0 < a →
--         ∀ G : Set (Space (h+3) × Space (h+3)), MeasurableSet G →
--         (∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z-c‖ ≤ 1/(4*a)) →
--         (∀ᵐ z ∂μ, ‖z-c‖ ≤ 1/(4*a)) →
--         (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x ((1/(2:ℝ)^j)/a)) ≤
--           ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
--         (∀ᵐ z ∂μ,
--           (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N →
--             ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+3)) < 1/(2:ℝ)^j} ≤
--               ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) ∧
--           (∀ w : Sphere (h+3), ∀ u : ℝ, 1/(2:ℝ)^N ≤ u → u ≤ 1 →
--             ν {x | (z,x) ∈ G ∧ |inner ℝ (w:Space (h+3)) (normalize (x-z))| ≤ u} ≤
--               ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*u^ζ))) →
--         ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/(a*r) ≤ 1/(2:ℝ)^N →
--         (a*H)*θ ≤ 1/(2:ℝ)^N →
--         (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖c-x‖ ∧ ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) →
--         ∃ G' : Set (Space (h+3) × Space (h+3)), MeasurableSet G' ∧ G' ⊆ G ∧
--           (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^N)^b) ∧
--           ∀ p ∈ G', radialCollisionMass μ θ p ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^((h+1:ℝ)+b/2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.Space` and `OAI.Falconer.Sphere` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedFiniteLoomisWhitney` (definitions bundle `OAIQ088F001` of this split); `OAI.Falconer.radialCollisionMass` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proofs of `OAI.Falconer.Regularization.endpoint_one_scale_gain`, `OAI_Falconer_Regularization_endpoint_source_class_middle_pruning` and `OAI_Falconer_Regularization_endpoint_two_sided_one_scale` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/EndpointOriginalMiddle.lean (declaration OAI.Falconer.endpoint_original_middle_pruning)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem endpoint_original_middle_pruning (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ : ℝ} (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+3)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (_w₀ : Sphere (h+3)) (c : Space (h+3)) (a : ℝ), 0 < a →
      ∀ G : Set (Space (h+3) × Space (h+3)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z-c‖ ≤ 1/(4*a)) →
      (∀ᵐ z ∂μ, ‖z-c‖ ≤ 1/(4*a)) →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x ((1/(2:ℝ)^j)/a)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ,
        (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+3)) < 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) ∧
        (∀ w : Sphere (h+3), ∀ u : ℝ, 1/(2:ℝ)^N ≤ u → u ≤ 1 →
          ν {x | (z,x) ∈ G ∧ |inner ℝ (w:Space (h+3)) (normalize (x-z))| ≤ u} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*u^ζ))) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/(a*r) ≤ 1/(2:ℝ)^N →
      (a*H)*θ ≤ 1/(2:ℝ)^N →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖c-x‖ ∧ ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+3) × Space (h+3)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^N)^b) ∧
        ∀ p ∈ G', radialCollisionMass μ θ p ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^((h+1:ℝ)+b/2)) := by
  sorry

end Falconer

end OAI
end

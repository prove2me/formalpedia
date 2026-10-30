-- Prove2me | Theorems.Thm_OAI_Falconer_endpoint_spherical_preparation
-- name    : OAI.Falconer.endpoint_spherical_preparation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:48:46.396804+00:00
-- url     : https://prove2.me/theorems/54223eb0-8418-495d-91c8-ddb77b7d276f
-- title:
--   OAI.Falconer.endpoint_spherical_preparation: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.endpoint_spherical_preparation` of [lean/OAI/MeasureTheory/Falconer/Estimates/EndpointSphericalPreparation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/EndpointSphericalPreparation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set Metric MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem endpoint_spherical_preparation (hLW : PublishedFiniteLoomisWhitney)
--       {ζ a : ℝ} (hζ : 0 < ζ) (ha : 0 < a) :
--       ∃ ε c₁ c₂ : ℝ, 0 < ε ∧ 0 < c₁ ∧ 0 < c₂ ∧ ∃ N₀ : ℕ,
--         ∀ N ≥ N₀, ∀ (ν : Measure (Sphere (h+3))) [IsProbabilityMeasure ν],
--         (∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space (h+2))) ≤ 1/8) →
--         (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (ball w (1/(2:ℝ)^j)) ≤
--           ENNReal.ofReal (((2:ℝ)^N)^ε*(1/(2:ℝ)^j)^((h+1:ℕ):ℝ))) →
--         (∀ w : Sphere (h+3), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
--           ν {v : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (v:Space (h+3))| ≤ r} ≤
--             ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
--         let ν₀ := Measure.map gnomonicCoordinates ν
--         ∃ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G ∧
--           (∫⁻ A : Fin h → Space (h+3),
--             ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
--               (gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N))) Gᶜ ∂gaussianRows (h+3) h) ≤
--             ENNReal.ofReal (((2:ℝ)^N)^(-c₁)) ∧
--           (∫⁻ A : Fin h → Space (h+3),
--             ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
--               ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
--                 (gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N))))
--               (badChartTriples G (2*((2:ℝ)^N)^(-a))) ∂gaussianRows (h+3) h) ≤
--             ENNReal.ofReal (((2:ℝ)^N)^(-c₂))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.gnomonicChart` and `OAI.Falconer.gnomonicCoordinates` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedFiniteLoomisWhitney` (definitions bundle `OAIQ088F001` of this split); `OAI.Falconer.badChartTriples`, `OAI.Falconer.gaussianChartSliceMeasure` and `OAI.Falconer.gaussianRows` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proofs of `OAI_Falconer_endpoint_dyadic_angular_gain` and `OAI.Falconer.endpoint_original_middle_pruning` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/EndpointSphericalPreparation.lean (declaration OAI.Falconer.endpoint_spherical_preparation)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {h : ℕ}

theorem endpoint_spherical_preparation (hLW : PublishedFiniteLoomisWhitney)
    {ζ a : ℝ} (hζ : 0 < ζ) (ha : 0 < a) :
    ∃ ε c₁ c₂ : ℝ, 0 < ε ∧ 0 < c₁ ∧ 0 < c₂ ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ν : Measure (Sphere (h+3))) [IsProbabilityMeasure ν],
      (∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space (h+2))) ≤ 1/8) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal (((2:ℝ)^N)^ε*(1/(2:ℝ)^j)^((h+1:ℕ):ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        ν {v : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (v:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      let ν₀ := Measure.map gnomonicCoordinates ν
      ∃ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G ∧
        (∫⁻ A : Fin h → Space (h+3),
          ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
            (gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N))) Gᶜ ∂gaussianRows (h+3) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c₁)) ∧
        (∫⁻ A : Fin h → Space (h+3),
          ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
            ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
              (gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N))))
            (badChartTriples G (2*((2:ℝ)^N)^(-a))) ∂gaussianRows (h+3) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c₂)) := by
  sorry

end Falconer

end OAI
end

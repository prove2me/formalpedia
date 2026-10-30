-- Prove2me | Theorems.Thm_OAI_Falconer_small_chart_weak_radial
-- name    : OAI.Falconer.small_chart_weak_radial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:42:00.095824+00:00
-- url     : https://prove2.me/theorems/f33be528-9dff-4bed-a47a-0e76f930245f
-- title:
--   OAI.Falconer.small_chart_weak_radial: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.small_chart_weak_radial` of [lean/OAI/MeasureTheory/Falconer/Radial/SmallChartWeakRadial.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Radial/SmallChartWeakRadial.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set Metric MeasureTheory NormedSpace`, `open scoped ENNReal`):
--
--   ```lean
--   theorem small_chart_weak_radial (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
--       {ζ ell e : ℝ} (hζ : 0 < ζ) (hell0 : 0 ≤ ell)
--       (hell : ell < ((n:ℝ)/(n+1))*(n:ℝ)) (he : 0 < e) :
--       ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
--         ∀ (μ : Measure (Space (n+1))) [IsProbabilityMeasure μ],
--         (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
--         (∀ x : Space (n+1), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
--           μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^(n:ℝ))) →
--         (∀ w : Space (n+1), ‖w‖ = 1 → ∀ a r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
--           μ {x | |inner ℝ w x-a| ≤ r} ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
--         ∃ G : Set (Space (n+1) × Space (n+1)), MeasurableSet G ∧
--           (∀ p z, (p,z) ∈ G → z ≠ p) ∧
--           (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
--           ∀ p, ∀ j : ℕ, j ≤ N → ∀ u : Space (n+1),
--             μ {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
--               ENNReal.ofReal (((2:ℝ)^N)^e*(3*(1/(2:ℝ)^j))^ell)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.Space` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedFiniteLoomisWhitney` (definitions bundle `OAIQ088F001` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.endpoint_spherical_preparation` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Radial/SmallChartWeakRadial.lean (declaration OAI.Falconer.small_chart_weak_radial)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F000
import Definitions.Def_OAIQ088F001

section

attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem small_chart_weak_radial (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    {ζ ell e : ℝ} (hζ : 0 < ζ) (hell0 : 0 ≤ ell)
    (hell : ell < ((n:ℝ)/(n+1))*(n:ℝ)) (he : 0 < e) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ : Measure (Space (n+1))) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
      (∀ x : Space (n+1), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^(n:ℝ))) →
      (∀ w : Space (n+1), ‖w‖ = 1 → ∀ a r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ {x | |inner ℝ w x-a| ≤ r} ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      ∃ G : Set (Space (n+1) × Space (n+1)), MeasurableSet G ∧
        (∀ p z, (p,z) ∈ G → z ≠ p) ∧
        (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ p, ∀ j : ℕ, j ≤ N → ∀ u : Space (n+1),
          μ {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
            ENNReal.ofReal (((2:ℝ)^N)^e*(3*(1/(2:ℝ)^j))^ell) := by
  sorry

end Falconer

end OAI
end

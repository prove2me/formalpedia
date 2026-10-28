-- Prove2me | Theorems.Thm_OAI_PlanarFPP_actual_grid_trial_probabilities
-- name    : OAI.PlanarFPP.actual_grid_trial_probabilities
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:40:13.868307+00:00
-- url     : https://prove2.me/theorems/da01a837-614e-4da6-90b2-251f4060f0a9
-- title:
--   OAI.PlanarFPP.actual_grid_trial_probabilities: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFPP.actual_grid_trial_probabilities` of [lean/OAI/Probability/FirstPassage/GridMeshes.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/GridMeshes.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFPP`, with `open Filter Set MeasureTheory`, `open scoped Topology`):
--
--   ```lean
--   theorem actual_grid_trial_probabilities (henv : ExponentialEnvironment P τ)
--       (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
--       (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
--       ∀ᶠ k : ℕ in atTop, ∀ j : ℕ,
--         j ≤ gridLastLevel (characteristicExponent P τ μ b q₀ k) →
--         ((1/16 : ℝ)^j*(characteristicLength P τ μ b q₀ k : ℝ) ≤
--           (characteristicLength P τ μ b q₀ (k-j) : ℝ)) →
--         q₀ < P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b))
--           (sourceCrossingK μ b) (gridWidth k j) (gridMesh (characteristicExponent P τ μ b q₀ k) j) 0}
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFPP.gridLastLevel` (definitions bundle `OAISPf000` of this split); `OAI.PlanarFPP.direction`, `OAI.PlanarFPP.gridMesh` and `OAI.PlanarFPP.gridWidth` (definitions bundle `OAISPf001` of this split); `OAI.PlanarFPP.characteristicExponent`, `OAI.PlanarFPP.characteristicLength`, `OAI.PlanarFPP.crossingEvent` and `OAI.PlanarFPP.sourceCrossingK` (definitions bundle `OAISPf002` of this split); `OAI.PlanarFPP.Edge`, `OAI.PlanarFPP.ExponentialEnvironment`, `OAI.PlanarFPP.IsTimeConstant`, `OAI.PlanarFPP.Plane`, `OAI.PlanarFPP.TimeConstantNorm` and `OAI.PlanarFPP.Vertex` (the published bundle `Def_PlanarFirstPassage`).
--
--   **Used by.** The proof of `OAI.PlanarFPP.actual_spatial_rare_scales` of this split imports it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/GridMeshes.lean (declaration OAI.PlanarFPP.actual_grid_trial_probabilities)

import Mathlib
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002

section

attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter Set MeasureTheory
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actual_grid_trial_probabilities (henv : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∀ᶠ k : ℕ in atTop, ∀ j : ℕ,
      j ≤ gridLastLevel (characteristicExponent P τ μ b q₀ k) →
      ((1/16 : ℝ)^j*(characteristicLength P τ μ b q₀ k : ℝ) ≤
        (characteristicLength P τ μ b q₀ (k-j) : ℝ)) →
      q₀ < P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b))
        (sourceCrossingK μ b) (gridWidth k j) (gridMesh (characteristicExponent P τ μ b q₀ k) j) 0} := by
  sorry

end PlanarFPP

end OAI
end

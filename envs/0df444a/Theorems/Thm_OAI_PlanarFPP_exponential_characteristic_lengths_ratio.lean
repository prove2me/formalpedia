-- Prove2me | Theorems.Thm_OAI_PlanarFPP_exponential_characteristic_lengths_ratio
-- name    : OAI.PlanarFPP.exponential_characteristic_lengths_ratio
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:41:34.689387+00:00
-- url     : https://prove2.me/theorems/e7b45be6-b22d-48ca-b710-736f5f5560ee
-- title:
--   OAI.PlanarFPP.exponential_characteristic_lengths_ratio: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFPP.exponential_characteristic_lengths_ratio` of [lean/OAI/Probability/FirstPassage/CharacteristicLengths.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/CharacteristicLengths.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFPP`, with `open Set Filter MeasureTheory`, `open scoped Topology`):
--
--   ```lean
--   theorem exponential_characteristic_lengths_ratio (h : ExponentialEnvironment P τ)
--       (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
--       (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
--       Tendsto (fun k : ℕ => (characteristicLength P τ μ b q k : ℝ)/(2 : ℝ)^k) atTop atTop
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFPP.characteristicLength` (definitions bundle `OAISPf002` of this split); `OAI.PlanarFPP.Edge`, `OAI.PlanarFPP.ExponentialEnvironment`, `OAI.PlanarFPP.IsTimeConstant`, `OAI.PlanarFPP.Plane` and `OAI.PlanarFPP.TimeConstantNorm` (the published bundle `Def_PlanarFirstPassage`).
--
--   **Used by.** The proofs of `OAI.PlanarFPP.actual_grid_trial_probabilities` and `OAI.PlanarFPP.actual_spatial_rare_scales` of this split import it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/CharacteristicLengths.lean (declaration OAI.PlanarFPP.exponential_characteristic_lengths_ratio)

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
open Set Filter MeasureTheory
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)

variable {P τ}

theorem exponential_characteristic_lengths_ratio (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (fun k : ℕ => (characteristicLength P τ μ b q k : ℝ)/(2 : ℝ)^k) atTop atTop := by
  sorry

end PlanarFPP

end OAI
end

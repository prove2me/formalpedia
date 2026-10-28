-- Prove2me | Theorems.Thm_OAI_PlanarFPP_exponential_characteristic_lengths_exist
-- name    : OAI.PlanarFPP.exponential_characteristic_lengths_exist
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:41:20.981864+00:00
-- url     : https://prove2.me/theorems/d708b10f-f362-49ff-8414-535591b590d2
-- title:
--   OAI.PlanarFPP.exponential_characteristic_lengths_exist: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFPP.exponential_characteristic_lengths_exist` of [lean/OAI/Probability/FirstPassage/CharacteristicLengths.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/CharacteristicLengths.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFPP`, with `open Set Filter MeasureTheory`, `open scoped Topology`):
--
--   ```lean
--   theorem exponential_characteristic_lengths_exist (h : ExponentialEnvironment P τ)
--       (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
--       (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) :
--       ∀ᶠ k : ℕ in atTop,
--         characteristicExponent P τ μ b q k ≤ 3*k ∧
--         P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b)) (sourceCrossingK μ b)
--           ((2 : ℝ)^k) (characteristicLength P τ μ b q k) 0} ≤ q
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFPP.direction` (definitions bundle `OAISPf001` of this split); `OAI.PlanarFPP.characteristicExponent`, `OAI.PlanarFPP.characteristicLength`, `OAI.PlanarFPP.crossingEvent` and `OAI.PlanarFPP.sourceCrossingK` (definitions bundle `OAISPf002` of this split); `OAI.PlanarFPP.Edge`, `OAI.PlanarFPP.ExponentialEnvironment`, `OAI.PlanarFPP.IsTimeConstant`, `OAI.PlanarFPP.Plane`, `OAI.PlanarFPP.TimeConstantNorm` and `OAI.PlanarFPP.Vertex` (the published bundle `Def_PlanarFirstPassage`).
--
--   **Used by.** The proofs of `OAI.PlanarFPP.actual_grid_trial_probabilities`, `OAI.PlanarFPP.actual_spatial_rare_scales` and `OAI.PlanarFPP.exponential_characteristic_lengths_ratio` of this split import it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/CharacteristicLengths.lean (declaration OAI.PlanarFPP.exponential_characteristic_lengths_exist)

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

theorem exponential_characteristic_lengths_exist (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) :
    ∀ᶠ k : ℕ in atTop,
      characteristicExponent P τ μ b q k ≤ 3*k ∧
      P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b)) (sourceCrossingK μ b)
        ((2 : ℝ)^k) (characteristicLength P τ μ b q k) 0} ≤ q := by
  sorry

end PlanarFPP

end OAI
end

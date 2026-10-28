-- Prove2me | Theorems.Thm_OAI_PlanarFPP_actual_spatial_rare_scales
-- name    : OAI.PlanarFPP.actual_spatial_rare_scales
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:40:17.840989+00:00
-- url     : https://prove2.me/theorems/ba6ac0c5-86ff-482d-baf9-b40defa79f0f
-- title:
--   OAI.PlanarFPP.actual_spatial_rare_scales: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFPP.actual_spatial_rare_scales` of [lean/OAI/Probability/FirstPassage/SpatialRareEvents.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/SpatialRareEvents.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFPP`, with `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology`):
--
--   ```lean
--   theorem actual_spatial_rare_scales (henv : ExponentialEnvironment P τ)
--       (b q₀ η : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hη : 0 < η)
--       (N : ℕ) (S D : ℝ) :
--       ∃ k : ℕ, N < k ∧ S ≤ (2 : ℝ)^k ∧
--         D*(2 : ℝ)^k ≤ (characteristicLength P τ actualSourceTimeConstant b q₀ k : ℝ) ∧
--         ∀ ih : ℤ×ℤ, P.real {ω | (fun e => τ e ω) ∈ spatialRareEvent b
--           (actualSourceTimeConstant (direction b)) (extremeSlope actualSourceTimeConstant b false)
--           (extremeSlope actualSourceTimeConstant b true) (sourceCrossingK actualSourceTimeConstant b) η k
--           (characteristicExponent P τ actualSourceTimeConstant b q₀ k) ih} ≤ 2*q₀
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFPP.direction` and `OAI.PlanarFPP.extremeSlope` (definitions bundle `OAISPf001` of this split); `OAI.PlanarFPP.actualSourceTimeConstant`, `OAI.PlanarFPP.characteristicExponent`, `OAI.PlanarFPP.characteristicLength`, `OAI.PlanarFPP.sourceCrossingK` and `OAI.PlanarFPP.spatialRareEvent` (definitions bundle `OAISPf002` of this split); `OAI.PlanarFPP.Edge` and `OAI.PlanarFPP.ExponentialEnvironment` (the published bundle `Def_PlanarFirstPassage`).
--
--   **Used by.** The proof of `OAI.PlanarFPP.actual_differentiable_horizontal` of this split imports it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/SpatialRareEvents.lean (declaration OAI.PlanarFPP.actual_spatial_rare_scales)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actual_spatial_rare_scales (henv : ExponentialEnvironment P τ)
    (b q₀ η : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hη : 0 < η)
    (N : ℕ) (S D : ℝ) :
    ∃ k : ℕ, N < k ∧ S ≤ (2 : ℝ)^k ∧
      D*(2 : ℝ)^k ≤ (characteristicLength P τ actualSourceTimeConstant b q₀ k : ℝ) ∧
      ∀ ih : ℤ×ℤ, P.real {ω | (fun e => τ e ω) ∈ spatialRareEvent b
        (actualSourceTimeConstant (direction b)) (extremeSlope actualSourceTimeConstant b false)
        (extremeSlope actualSourceTimeConstant b true) (sourceCrossingK actualSourceTimeConstant b) η k
        (characteristicExponent P τ actualSourceTimeConstant b q₀ k) ih} ≤ 2*q₀ := by
  sorry

end PlanarFPP

end OAI
end

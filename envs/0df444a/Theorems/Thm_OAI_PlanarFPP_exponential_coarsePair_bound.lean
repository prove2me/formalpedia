-- Prove2me | Theorems.Thm_OAI_PlanarFPP_exponential_coarsePair_bound
-- name    : OAI.PlanarFPP.exponential_coarsePair_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:41:48.572788+00:00
-- url     : https://prove2.me/theorems/879922d4-5047-42fd-ac5d-9910e24a0349
-- title:
--   OAI.PlanarFPP.exponential_coarsePair_bound: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFPP.exponential_coarsePair_bound` of [lean/OAI/Probability/FirstPassage/EndpointProbability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/EndpointProbability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFPP`, with `open Set Finset MeasureTheory ProbabilityTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem exponential_coarsePair_bound (henv : ExponentialEnvironment P τ)
--       (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
--       (b A R ε : ℝ) (hb : |b| ≤ 1) (hA : 0 < A) (hR : 0 ≤ R) (hε : 0 < ε)
--       (plus : Bool) (J : ℕ) (κ : ℝ) (hκ : 0 < κ) :
--       ∃ S D : ℝ, 1 ≤ S ∧ 0 < D ∧ ∀ k m : ℕ, S ≤ (2 : ℝ)^k →
--         D*(2 : ℝ)^k ≤ (gridMesh m J : ℝ) → ∀ ij ∈ coarsePairIndices A J,
--         P.real {ω | (fun e => τ e ω) ∈
--           coarsePairEvent b (μ (direction b)) (extremeSlope μ b plus) A R ε k m J ij} < κ
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFPP.coarsePairIndices`, `OAI.PlanarFPP.direction`, `OAI.PlanarFPP.extremeSlope` and `OAI.PlanarFPP.gridMesh` (definitions bundle `OAISPf001` of this split); `OAI.PlanarFPP.coarsePairEvent` (definitions bundle `OAISPf002` of this split); `OAI.PlanarFPP.Edge`, `OAI.PlanarFPP.ExponentialEnvironment`, `OAI.PlanarFPP.IsTimeConstant`, `OAI.PlanarFPP.Plane` and `OAI.PlanarFPP.TimeConstantNorm` (the published bundle `Def_PlanarFirstPassage`).
--
--   **Used by.** The proof of `OAI.PlanarFPP.exponential_arbitraryEndpoint_tendsto_of_grids` of this split imports it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/EndpointProbability.lean (declaration OAI.PlanarFPP.exponential_coarsePair_bound)

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
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_coarsePair_bound (henv : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (hA : 0 < A) (hR : 0 ≤ R) (hε : 0 < ε)
    (plus : Bool) (J : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ S D : ℝ, 1 ≤ S ∧ 0 < D ∧ ∀ k m : ℕ, S ≤ (2 : ℝ)^k →
      D*(2 : ℝ)^k ≤ (gridMesh m J : ℝ) → ∀ ij ∈ coarsePairIndices A J,
      P.real {ω | (fun e => τ e ω) ∈
        coarsePairEvent b (μ (direction b)) (extremeSlope μ b plus) A R ε k m J ij} < κ := by
  sorry

end PlanarFPP

end OAI
end

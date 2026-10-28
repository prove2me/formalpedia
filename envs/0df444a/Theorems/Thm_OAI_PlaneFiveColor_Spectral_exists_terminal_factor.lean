-- Prove2me | Theorems.Thm_OAI_PlaneFiveColor_Spectral_exists_terminal_factor
-- name    : OAI.PlaneFiveColor.Spectral.exists_terminal_factor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T12:56:59.219995+00:00
-- url     : https://prove2.me/theorems/5f7f2f73-439e-437f-801f-95318861d038
-- title:
--   OAI.PlaneFiveColor.Spectral.exists_terminal_factor: intermediate lemma from OpenAI, The Euclidean plane cannot be colored with five colors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EuclideanFiveColor.no_proper_five_coloring`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Euclidean plane cannot be colored with five colors*, OpenAI Math Release, September 23, 2026, result family 158, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlaneFiveColor.Spectral.exists_terminal_factor` of [lean/OAI/Geometry/PlaneColoring/CompactFactors/Stationary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PlaneColoring/CompactFactors/Stationary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlaneFiveColor.Spectral`, with `open MeasureTheory ProbabilityTheory EuclideanFiveColor`):
--
--   ```lean
--   theorem exists_terminal_factor (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ] :
--       ∃ p : X → OrbitSpace K, ∃ hp : Measurable p,
--         (∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) ∧ UniversalGood μ p ∧
--         ErgodicSMul K (X × X) (RelativeProduct.law μ p hp)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EuclideanFiveColor.OrbitSpace`, `OAI.EuclideanFiveColor.OrbitSpace.instMeasurableSpace`, `OAI.EuclideanFiveColor.OrbitSpace.instMulAction`, `OAI.EuclideanFiveColor.RelativeProduct.law` and `OAI.PlaneFiveColor.Spectral.K` (definitions bundle `OAIQ5T4000` of this split); `OAI.PlaneFiveColor.Spectral.UniversalGood` (definitions bundle `OAIQ5T4002` of this split).
--
--   **Used by.** The proof of `OAI.EuclideanFiveColor.proper_to_borel_weak` of this split imports it.
-- source:
--   OpenAI, The Euclidean plane cannot be colored with five colors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 158; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PlaneColoring/CompactFactors/Stationary.lean (declaration OAI.PlaneFiveColor.Spectral.exists_terminal_factor)

import Mathlib
import Definitions.Def_OAIQ5T4002

section

attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.RelativeProduct.law_probability_add _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.PlaneFiveColor.Spectral.rotErgodic _root_.OAI.PlaneFiveColor.Spectral.rotInvariant _root_.OAI.PlaneFiveColor.Spectral.rotMeasurable _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory EuclideanFiveColor

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MulAction K X] [MeasurableConstSMul K X]

theorem exists_terminal_factor (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ] :
    ∃ p : X → OrbitSpace K, ∃ hp : Measurable p,
      (∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) ∧ UniversalGood μ p ∧
      ErgodicSMul K (X × X) (RelativeProduct.law μ p hp) := by
  sorry

end PlaneFiveColor.Spectral

end

end OAI
end

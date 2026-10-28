-- Prove2me | Theorems.Thm_OAI_PlaneFiveColor_Spectral_ambient_uniform_precision_contradiction
-- name    : OAI.PlaneFiveColor.Spectral.ambient_uniform_precision_contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T12:57:32.70026+00:00
-- url     : https://prove2.me/theorems/e1bc0545-19cf-4b44-9f16-aee48ecc4b18
-- title:
--   OAI.PlaneFiveColor.Spectral.ambient_uniform_precision_contradiction: intermediate lemma from OpenAI, The Euclidean plane cannot be colored with five colors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EuclideanFiveColor.no_proper_five_coloring`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Euclidean plane cannot be colored with five colors*, OpenAI Math Release, September 23, 2026, result family 158, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlaneFiveColor.Spectral.ambient_uniform_precision_contradiction` of [lean/OAI/Geometry/PlaneColoring/CompactFactors/ConditionalLimits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PlaneColoring/CompactFactors/ConditionalLimits.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlaneFiveColor.Spectral`, with `open scoped ComplexConjugate`, `open scoped BigOperators`, `open scoped BigOperators BoundedContinuousFunction`, `open Filter Topology`, `open MeasureTheory Filter`, `open scoped ENNReal ComplexConjugate`, `open MeasureTheory ProbabilityTheory`, `open scoped ComplexConjugate`, `open scoped BigOperators`, `open scoped BigOperators`, `open Polynomial`, `open MeasureTheory`, `open scoped BigOperators`, `open MeasureTheory`, `open scoped BigOperators`, `open MeasureTheory`, `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators`, `open MeasureTheory`, `open scoped BigOperators ComplexConjugate`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal BigOperators`, `open MeasureTheory Filter`, `open scoped Topology ENNReal NNReal`, `open MeasureTheory`, `open scoped ENNReal`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal`, `open MeasureTheory ProbabilityTheory`, `open MeasureTheory ProbabilityTheory EuclideanFiveColor`, `open scoped BigOperators ENNReal`):
--
--   ```lean
--   theorem ambient_uniform_precision_contradiction
--       (μ : Measure X) [IsProbabilityMeasure μ]
--       (p : X → Y) (q : X → W) (b : X → D)
--       (hp : Measurable p) (hq : Measurable q) (hb : Measurable b)
--       (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
--       (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
--         (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i))
--       (hwild : IsWild (DifferenceFourier.differenceLaw (μ.map (q))
--         (condDistrib b (q) μ)))
--       (ρ c : ℝ) (N : ℕ) (hρ : 0 < ρ) (hc : 0 < c) (hN : 0 < N)
--       (harc : ∀ (ω : Measure Circle) [IsProbabilityMeasure ω],
--         (∀ n, 0 < n → n ≤ N → ‖∫ w, (w : ℂ)^n ∂ω‖ < c) →
--         ω.real {w | ‖(w : ℂ)-1‖ ≤ 4*ρ} < 1/(4*(m : ℝ)^2))
--       (happrox : AmbientEncodingAt μ p q b m (((ρ^m/(m : ℝ))/100)/100)) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.EuclideanFiveColor.DifferenceFourier.differenceLaw`, `OAI.PlaneFiveColor.Spectral.D`, `OAI.PlaneFiveColor.Spectral.DiscreteE`, `OAI.PlaneFiveColor.Spectral.instMeasurableSpaceD` and `OAI.PlaneFiveColor.Spectral.instTopologicalSpaceDiscreteE` (definitions bundle `OAIQ5T4000` of this split); `OAI.PlaneFiveColor.Spectral.instMeasurableSpaceCircle_solutions_3` (definitions bundle `OAIQ5T4001` of this split); `OAI.PlaneFiveColor.Spectral.AmbientEncodingAt`, `OAI.PlaneFiveColor.Spectral.IsWild` and `OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace` (definitions bundle `OAIQ5T4002` of this split).
--
--   **Used by.** The proof of `OAI.PlaneFiveColor.Spectral.exists_terminal_factor` of this split imports it.
-- source:
--   OpenAI, The Euclidean plane cannot be colored with five colors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 158; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PlaneColoring/CompactFactors/ConditionalLimits.lean (declaration OAI.PlaneFiveColor.Spectral.ambient_uniform_precision_contradiction)

import Mathlib
import Definitions.Def_OAIQ5T4002

section

attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.K_countable _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.PlaneFiveColor.Spectral.rotErgodic _root_.OAI.PlaneFiveColor.Spectral.rotInvariant _root_.OAI.PlaneFiveColor.Spectral.rotMeasurable _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace PlaneFiveColor.Spectral

open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal
variable {X Y W : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

attribute [local instance] OAI.PlaneFiveColor.Spectral.instMeasurableSpaceCircle_solutions_3
omit [StandardBorelSpace Y] [Nonempty Y] in
theorem ambient_uniform_precision_contradiction
    (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → Y) (q : X → W) (b : X → D)
    (hp : Measurable p) (hq : Measurable q) (hb : Measurable b)
    (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i))
    (hwild : IsWild (DifferenceFourier.differenceLaw (μ.map (q))
      (condDistrib b (q) μ)))
    (ρ c : ℝ) (N : ℕ) (hρ : 0 < ρ) (hc : 0 < c) (hN : 0 < N)
    (harc : ∀ (ω : Measure Circle) [IsProbabilityMeasure ω],
      (∀ n, 0 < n → n ≤ N → ‖∫ w, (w : ℂ)^n ∂ω‖ < c) →
      ω.real {w | ‖(w : ℂ)-1‖ ≤ 4*ρ} < 1/(4*(m : ℝ)^2))
    (happrox : AmbientEncodingAt μ p q b m (((ρ^m/(m : ℝ))/100)/100)) : False := by
  sorry

end PlaneFiveColor.Spectral

end

end OAI
end

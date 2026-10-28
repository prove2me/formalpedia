-- Prove2me | Theorems.Thm_OAI_PlaneFiveColor_Spectral_radial_positive_near_zero
-- name    : OAI.PlaneFiveColor.Spectral.radial_positive_near_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T12:57:44.935578+00:00
-- url     : https://prove2.me/theorems/48d070e9-55b6-42fa-963e-024eb12df42d
-- title:
--   OAI.PlaneFiveColor.Spectral.radial_positive_near_zero: intermediate lemma from OpenAI, The Euclidean plane cannot be colored with five colors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EuclideanFiveColor.no_proper_five_coloring`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Euclidean plane cannot be colored with five colors*, OpenAI Math Release, September 23, 2026, result family 158, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlaneFiveColor.Spectral.radial_positive_near_zero` of [lean/OAI/Geometry/PlaneColoring/PlaneSpectrum/RadialEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PlaneColoring/PlaneSpectrum/RadialEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlaneFiveColor.Spectral`, with `open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor`, `open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction`, `open EuclideanFiveColor.BoundedMeasurable`):
--
--   ```lean
--   lemma radial_positive_near_zero (r : F) (hr : 0 < r) (hm : massReal μ q r ≠ 0) :
--       ∃ δ : F, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
--         ∀ s : F, 0 < s → s < δ → ε ≤ massReal μ q s
--   ```
--
--   **Definitions.** The statement is written with `OAI.EuclideanFiveColor.RelativeProduct.law`, `OAI.PlaneFiveColor.Spectral.D`, `OAI.PlaneFiveColor.Spectral.DiscreteE`, `OAI.PlaneFiveColor.Spectral.F`, `OAI.PlaneFiveColor.Spectral.K`, `OAI.PlaneFiveColor.Spectral.Rot`, `OAI.PlaneFiveColor.Spectral.instMeasurableSpaceD`, `OAI.PlaneFiveColor.Spectral.instMulActionSubtypeCircleMemSubgroupKD`, `OAI.PlaneFiveColor.Spectral.instTopologicalSpaceDiscreteE` and `OAI.PlaneFiveColor.Spectral.rotAction` (definitions bundle `OAIQ5T4000` of this split); `OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace` and `OAI.PlaneFiveColor.Spectral.massReal` (definitions bundle `OAIQ5T4002` of this split).
--
--   **Used by.** The proof of `OAI.EuclideanFiveColor.proper_to_borel_weak` of this split imports it.
-- source:
--   OpenAI, The Euclidean plane cannot be colored with five colors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 158; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PlaneColoring/PlaneSpectrum/RadialEnergy.lean (declaration OAI.PlaneFiveColor.Spectral.radial_positive_near_zero)

import Mathlib
import Definitions.Def_OAIQ5T4002

section

attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.Spectral.instCountableRot _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]

include hq hqcov in
lemma radial_positive_near_zero (r : F) (hr : 0 < r) (hm : massReal μ q r ≠ 0) :
    ∃ δ : F, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ s : F, 0 < s → s < δ → ε ≤ massReal μ q s := by
  sorry

end PlaneFiveColor.Spectral
end

end OAI
end

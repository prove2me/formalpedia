-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_measurable_weighted_area_bound
-- name    : OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:06:07.292472+00:00
-- url     : https://prove2.me/theorems/ee5ac022-41f3-4bb5-b651-4db493a03877
-- title:
--   OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound` of [lean/OAI/Geometry/CubicTorus/Profiles/NestingBaseline.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/NestingBaseline.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_measurable_weighted_area_bound {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
--       (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
--         H*directionalFlux E D.coordinate D.function) (i : Fin 3)
--       (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
--       {γ : ℝ → ℝ} (hγ : Measurable γ) (hγn : ∀ x,0≤γ x)
--       (hγw : ∀ᵐ t,γ ((axialSliceVolume (openRepresentative E) i t).toReal)≤
--         Nesting.weight (actualAxialFlux (openRepresentative E) μ H i t/axialPerimeterDensity μ i t))
--       {τ : ℝ} (hτ : τ∈Icc (0 : ℝ) 1) :
--       Nesting.lambda*axialTransverseMass μ i+
--         2*|∫ y in (axialSliceVolume (openRepresentative E) i 0).toReal..
--           (axialSliceVolume (openRepresentative E) i (τ : AxisCircle)).toReal,γ y|≤
--         (perimeter E).toReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.actualAxialFlux`, `OAI.CubicTorus.axialAreaMarginal`, `OAI.CubicTorus.axialPerimeterDensity`, `OAI.CubicTorus.axialSliceVolume`, `OAI.CubicTorus.axialTransverseMass`, `OAI.CubicTorus.directionalFlux`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.Nesting.lambda`, `OAI.CubicTorus.Nesting.weight`, `OAI.CubicTorus.Periodic.Variation` and `OAI.CubicTorus.Periodic.normalFirstVariation` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.perimeter` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_missing_neighbor_sharp_area_flux` and `OAI.CubicTorus.isMinimizerAt_nesting_cubic_gain` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/NestingBaseline.lean (declaration OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_measurable_weighted_area_bound {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {γ : ℝ → ℝ} (hγ : Measurable γ) (hγn : ∀ x,0≤γ x)
    (hγw : ∀ᵐ t,γ ((axialSliceVolume (openRepresentative E) i t).toReal)≤
      Nesting.weight (actualAxialFlux (openRepresentative E) μ H i t/axialPerimeterDensity μ i t))
    {τ : ℝ} (hτ : τ∈Icc (0 : ℝ) 1) :
    Nesting.lambda*axialTransverseMass μ i+
      2*|∫ y in (axialSliceVolume (openRepresentative E) i 0).toReal..
        (axialSliceVolume (openRepresentative E) i (τ : AxisCircle)).toReal,γ y|≤
      (perimeter E).toReal := by
  sorry

end CubicTorus

end
end

end

end OAI
end

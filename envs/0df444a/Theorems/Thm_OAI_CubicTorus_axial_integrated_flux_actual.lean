-- Prove2me | Theorems.Thm_OAI_CubicTorus_axial_integrated_flux_actual
-- name    : OAI.CubicTorus.axial_integrated_flux_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:54:44.923741+00:00
-- url     : https://prove2.me/theorems/59802056-c168-4923-b7fd-944b84723ba6
-- title:
--   OAI.CubicTorus.axial_integrated_flux_actual: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.axial_integrated_flux_actual` of [lean/OAI/Geometry/CubicTorus/Profiles/SharpSectionWeight.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/SharpSectionWeight.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma axial_integrated_flux_actual {E : Set Torus} (hE : MeasurableSet E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
--       (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
--         H*directionalFlux E D.coordinate D.function) (i : Fin 3)
--       (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
--       Nesting.lambda*axialTransverseMass μ i+
--         (∫ t,Nesting.weight (actualAxialFlux E μ H i t/axialPerimeterDensity μ i t)*
--           |axialNormalDensity μ i t|)≤(perimeter E).toReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.actualAxialFlux`, `OAI.CubicTorus.axialAreaMarginal`, `OAI.CubicTorus.axialNormalDensity`, `OAI.CubicTorus.axialPerimeterDensity`, `OAI.CubicTorus.axialTransverseMass`, `OAI.CubicTorus.directionalFlux`, `OAI.CubicTorus.Nesting.lambda`, `OAI.CubicTorus.Nesting.weight`, `OAI.CubicTorus.Periodic.Variation` and `OAI.CubicTorus.Periodic.normalFirstVariation` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.perimeter` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound` and `OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/SharpSectionWeight.lean (declaration OAI.CubicTorus.axial_integrated_flux_actual)

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

lemma axial_integrated_flux_actual {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    Nesting.lambda*axialTransverseMass μ i+
      (∫ t,Nesting.weight (actualAxialFlux E μ H i t/axialPerimeterDensity μ i t)*
        |axialNormalDensity μ i t|)≤(perimeter E).toReal := by
  sorry

end CubicTorus

end
end

end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_missing_neighbor_sharp_area_flux
-- name    : OAI.CubicTorus.isMinimizerAt_missing_neighbor_sharp_area_flux
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:31:47.40098+00:00
-- url     : https://prove2.me/theorems/667abc31-273a-4581-b5dc-12a02b2f8d53
-- title:
--   OAI.CubicTorus.isMinimizerAt_missing_neighbor_sharp_area_flux: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_missing_neighbor_sharp_area_flux` of [lean/OAI/Geometry/CubicTorus/Profiles/NestingBaseline.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/NestingBaseline.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_missing_neighbor_sharp_area_flux {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
--       (b : Fin 3 →Bool)
--       (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
--         quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ} (hH0 : 0≤H)
--       (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
--         H*directionalFlux E D.coordinate D.function)
--       (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
--       (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
--       Nesting.lambda*H*V+2*(∫ s in (0 : ℝ)..
--         (axialSliceVolume (openRepresentative E) i (octantHeight b i 0 : AxisCircle)).toReal,
--           sharpSectionWeight H s)≤(perimeter E).toReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.OrientedCoordinateLE`, `OAI.CubicTorus.axialAreaMarginal`, `OAI.CubicTorus.axialSliceVolume`, `OAI.CubicTorus.axisReflection`, `OAI.CubicTorus.directionalFlux`, `OAI.CubicTorus.octantHeight`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.orientedUpperVertex`, `OAI.CubicTorus.sharpSectionWeight`, `OAI.CubicTorus.LatticeIsometry`, `OAI.CubicTorus.Nesting.lambda`, `OAI.CubicTorus.Periodic.Variation` and `OAI.CubicTorus.Periodic.normalFirstVariation` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.upperOctant` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.perimeter`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_cylinder_contact_not_three_vertices` and `OAI.CubicTorus.isMinimizerAt_fixed_downset_not_three_vertices` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/NestingBaseline.lean (declaration OAI.CubicTorus.isMinimizerAt_missing_neighbor_sharp_area_flux)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003

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

theorem isMinimizerAt_missing_neighbor_sharp_area_flux {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ} (hH0 : 0≤H)
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    Nesting.lambda*H*V+2*(∫ s in (0 : ℝ)..
      (axialSliceVolume (openRepresentative E) i (octantHeight b i 0 : AxisCircle)).toReal,
        sharpSectionWeight H s)≤(perimeter E).toReal := by
  sorry

end CubicTorus

end
end

end

end OAI
end

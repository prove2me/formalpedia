-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_section_extent_perimeter
-- name    : OAI.CubicTorus.isMinimizerAt_section_extent_perimeter
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:36:17.733543+00:00
-- url     : https://prove2.me/theorems/85e5ad24-63f4-4648-b14a-33da97a746dc
-- title:
--   OAI.CubicTorus.isMinimizerAt_section_extent_perimeter: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_section_extent_perimeter` of [lean/OAI/Geometry/CubicTorus/Profiles/PlanarRadialDownset.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/PlanarRadialDownset.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_section_extent_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hmin : IsMinimizerAt V E)
--       (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
--       {b : Fin 3 →Bool}
--       (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
--         quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
--       (i : Fin 3) (t : ℝ)
--       (hin : quotientMap (axialSectionCorner b i t (fun _ ↦ false))∈openRepresentative E)
--       (hout0 : quotientMap (axialSectionCorner b i t (fun j ↦ j==0))∉closure (openRepresentative E))
--       (hout1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∉closure (openRepresentative E)) :
--       ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
--         (∀ y∈centeredAxialSlice (openRepresentative E) b i (t : AxisCircle),‖y 1‖<L) ∧
--         ENNReal.ofReal (volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))/L+Real.pi*L)≤
--           planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.OrientedCoordinateLE`, `OAI.CubicTorus.TransverseProduct`, `OAI.CubicTorus.axialSectionCorner`, `OAI.CubicTorus.axialSlice`, `OAI.CubicTorus.axisReflection`, `OAI.CubicTorus.centeredAxialSlice`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.planarTorusPerimeter` and `OAI.CubicTorus.LatticeIsometry` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.upperOctant` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_bottom_extent_calibration`, `OAI.CubicTorus.isMinimizerAt_section_improved_profile` and `OAI.CubicTorus.isMinimizerAt_section_planar_profile` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/PlanarRadialDownset.lean (declaration OAI.CubicTorus.isMinimizerAt_section_extent_perimeter)

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

theorem isMinimizerAt_section_extent_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (t : ℝ)
    (hin : quotientMap (axialSectionCorner b i t (fun _ ↦ false))∈openRepresentative E)
    (hout0 : quotientMap (axialSectionCorner b i t (fun j ↦ j==0))∉closure (openRepresentative E))
    (hout1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∉closure (openRepresentative E)) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈centeredAxialSlice (openRepresentative E) b i (t : AxisCircle),‖y 1‖<L) ∧
      ENNReal.ofReal (volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))/L+Real.pi*L)≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  sorry

end CubicTorus

end
end

end

end OAI
end

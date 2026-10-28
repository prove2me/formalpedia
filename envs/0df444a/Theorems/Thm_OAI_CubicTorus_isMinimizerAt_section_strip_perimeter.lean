-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_section_strip_perimeter
-- name    : OAI.CubicTorus.isMinimizerAt_section_strip_perimeter
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:37:28.770956+00:00
-- url     : https://prove2.me/theorems/e22d7b30-3b91-4a9b-870f-ca7b89fc2fb9
-- title:
--   OAI.CubicTorus.isMinimizerAt_section_strip_perimeter: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_section_strip_perimeter` of [lean/OAI/Geometry/CubicTorus/Reflection/AxialSectionCorner.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/AxialSectionCorner.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_section_strip_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hmin : IsMinimizerAt V E)
--       (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
--       {b : Fin 3 → Bool}
--       (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
--         quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
--       (i : Fin 3) (j : Fin 2) {t : ℝ} (ht : t∈Icc (1/2 : ℝ) 1)
--       (hin : quotientMap (axialSectionCorner b i t (fun k ↦ if k=j then false else true))∈openRepresentative E)
--       (hout : quotientMap (axialSectionCorner b i t (fun k ↦ if k=j then true else false))∉closure (openRepresentative E)) :
--       (2 : ℝ≥0∞)≤planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.OrientedCoordinateLE`, `OAI.CubicTorus.axialSectionCorner`, `OAI.CubicTorus.axialSlice`, `OAI.CubicTorus.axisReflection`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.planarTorusPerimeter` and `OAI.CubicTorus.LatticeIsometry` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.upperOctant` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_section_planar_profile` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/AxialSectionCorner.lean (declaration OAI.CubicTorus.isMinimizerAt_section_strip_perimeter)

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

theorem isMinimizerAt_section_strip_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (j : Fin 2) {t : ℝ} (ht : t∈Icc (1/2 : ℝ) 1)
    (hin : quotientMap (axialSectionCorner b i t (fun k ↦ if k=j then false else true))∈openRepresentative E)
    (hout : quotientMap (axialSectionCorner b i t (fun k ↦ if k=j then true else false))∉closure (openRepresentative E)) :
    (2 : ℝ≥0∞)≤planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  sorry

end CubicTorus

end
end

end

end OAI
end

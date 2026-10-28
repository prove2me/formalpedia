-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_section_planar_profile
-- name    : OAI.CubicTorus.isMinimizerAt_section_planar_profile
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:37:33.772245+00:00
-- url     : https://prove2.me/theorems/fc0d9fb5-457d-4c24-9132-6aecfac056a4
-- title:
--   OAI.CubicTorus.isMinimizerAt_section_planar_profile: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_section_planar_profile` of [lean/OAI/Geometry/CubicTorus/Profiles/NestingEndpointBound.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/NestingEndpointBound.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_section_planar_profile {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hmin : IsMinimizerAt V E)
--       (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
--       {b : Fin 3 →Bool}
--       (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
--         quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
--       (i : Fin 3) {t : ℝ} (ht : t∈Icc (1/2 : ℝ) 1)
--       (hc : ∀ n : Fin 2 →Bool,quotientMap (axialSectionCorner b i t n)∉frontier (openRepresentative E))
--       (hn : volume (axialSlice (frontier (openRepresentative E)) i (t : AxisCircle))=0) :
--       ENNReal.ofReal (unitPlanarProfile (volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))))≤
--         planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.OrientedCoordinateLE`, `OAI.CubicTorus.TransverseProduct`, `OAI.CubicTorus.axialSectionCorner`, `OAI.CubicTorus.axialSlice`, `OAI.CubicTorus.axisReflection`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.planarTorusPerimeter`, `OAI.CubicTorus.unitPlanarProfile` and `OAI.CubicTorus.LatticeIsometry` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.upperOctant` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_planar_profile_circle` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/NestingEndpointBound.lean (declaration OAI.CubicTorus.isMinimizerAt_section_planar_profile)

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

theorem isMinimizerAt_section_planar_profile {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) {t : ℝ} (ht : t∈Icc (1/2 : ℝ) 1)
    (hc : ∀ n : Fin 2 →Bool,quotientMap (axialSectionCorner b i t n)∉frontier (openRepresentative E))
    (hn : volume (axialSlice (frontier (openRepresentative E)) i (t : AxisCircle))=0) :
    ENNReal.ofReal (unitPlanarProfile (volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))))≤
      planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  sorry

end CubicTorus

end
end

end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_section_improved_profile
-- name    : OAI.CubicTorus.isMinimizerAt_section_improved_profile
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:36:25.431459+00:00
-- url     : https://prove2.me/theorems/7d22d2a8-db22-43ba-8d4b-8ba7f31d45db
-- title:
--   OAI.CubicTorus.isMinimizerAt_section_improved_profile: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_section_improved_profile` of [lean/OAI/Geometry/CubicTorus/Profiles/SmoothSeamProbability.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/SmoothSeamProbability.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_section_improved_profile {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hmin : IsMinimizerAt V E)
--       (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
--       {b : Fin 3 →Bool}
--       (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
--         quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
--       (i : Fin 3) {t : ℝ} (_ht : t∈Icc (1/2 : ℝ) 1)
--       (hc : ∀ n : Fin 2 →Bool,quotientMap (axialSectionCorner b i t n)∉frontier (openRepresentative E))
--       (hn : volume (axialSlice (frontier (openRepresentative E)) i (t : AxisCircle))=0)
--       {e δ q u : ℝ} (he : 0≤e) (hδ : δ∈Icc 0 Shape.dm) (hq : q∈Icc 0 1)
--       (hu : u≤1-1/Real.pi) (heq : e≤u-δ)
--       (hs : volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))=u-δ+δ*q)
--       (hslo : (38/100 : ℝ)<volume.real (axialSlice (openRepresentative E) i (t : AxisCircle)))
--       (hedge : ∀ j : Fin 2,∀ y∈closure (centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)),
--         (∀ k : Fin 2,k≠j →y k=((1/2 : ℝ) : AxisCircle)) →2*‖y j‖≤e) :
--       ENNReal.ofReal (2*Real.sqrt (1+Shape.c*δ^2*Shape.shape q))≤
--         planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.OrientedCoordinateLE`, `OAI.CubicTorus.TransverseProduct`, `OAI.CubicTorus.axialSectionCorner`, `OAI.CubicTorus.axialSlice`, `OAI.CubicTorus.axisReflection`, `OAI.CubicTorus.centeredAxialSlice`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.planarTorusPerimeter`, `OAI.CubicTorus.LatticeIsometry`, `OAI.CubicTorus.Shape.c`, `OAI.CubicTorus.Shape.dm` and `OAI.CubicTorus.Shape.shape` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.upperOctant` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_nesting_improved_profile_circle` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/SmoothSeamProbability.lean (declaration OAI.CubicTorus.isMinimizerAt_section_improved_profile)

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

theorem isMinimizerAt_section_improved_profile {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) {t : ℝ} (_ht : t∈Icc (1/2 : ℝ) 1)
    (hc : ∀ n : Fin 2 →Bool,quotientMap (axialSectionCorner b i t n)∉frontier (openRepresentative E))
    (hn : volume (axialSlice (frontier (openRepresentative E)) i (t : AxisCircle))=0)
    {e δ q u : ℝ} (he : 0≤e) (hδ : δ∈Icc 0 Shape.dm) (hq : q∈Icc 0 1)
    (hu : u≤1-1/Real.pi) (heq : e≤u-δ)
    (hs : volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))=u-δ+δ*q)
    (hslo : (38/100 : ℝ)<volume.real (axialSlice (openRepresentative E) i (t : AxisCircle)))
    (hedge : ∀ j : Fin 2,∀ y∈closure (centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)),
      (∀ k : Fin 2,k≠j →y k=((1/2 : ℝ) : AxisCircle)) →2*‖y j‖≤e) :
    ENNReal.ofReal (2*Real.sqrt (1+Shape.c*δ^2*Shape.shape q))≤
      planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  sorry

end CubicTorus

end
end

end

end OAI
end

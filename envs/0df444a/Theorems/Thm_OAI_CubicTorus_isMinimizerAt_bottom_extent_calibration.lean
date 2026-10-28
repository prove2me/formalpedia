-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_bottom_extent_calibration
-- name    : OAI.CubicTorus.isMinimizerAt_bottom_extent_calibration
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:28:53.522983+00:00
-- url     : https://prove2.me/theorems/f65d586b-27b4-449a-949f-74b3495e77ee
-- title:
--   OAI.CubicTorus.isMinimizerAt_bottom_extent_calibration: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_bottom_extent_calibration` of [lean/OAI/Geometry/CubicTorus/Reflection/AxialAreaDensity.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/AxialAreaDensity.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_bottom_extent_calibration {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
--       (b : Fin 3 →Bool)
--       (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
--         quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
--       (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
--         (∀ m x,F (x+latticeVector m)=F x) →
--         (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
--           H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
--       (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
--       (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
--       (hout : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun _ ↦ true))∉closure (openRepresentative E))
--       (hin0 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==0))∈openRepresentative E)
--       (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E) :
--       let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
--       0<H*s ∧ Real.pi*(1-s)≤((H/2)*s)^2 ∧
--         ∃ L : ℝ,L∈Ioo 0 1 ∧
--           (∀ y∈centeredAxialSlice (openRepresentative Eᶜ) (fun k ↦ !b k) i (octantHeight b i 0 : AxisCircle),2*‖y 1‖<L) ∧
--           (1-s)/L+Real.pi*L/4≤(H/2)*s
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.OrientedCoordinateLE`, `OAI.CubicTorus.TransverseProduct`, `OAI.CubicTorus.axialAreaMarginal`, `OAI.CubicTorus.axialSectionCorner`, `OAI.CubicTorus.axialSlice`, `OAI.CubicTorus.axisReflection`, `OAI.CubicTorus.centeredAxialSlice`, `OAI.CubicTorus.octantHeight`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.orientedUpperVertex`, `OAI.CubicTorus.tangentialDivergence` and `OAI.CubicTorus.LatticeIsometry` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.upperOctant` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_bottom_both_extents` and `OAI_CubicTorus_isMinimizerAt_nesting_area_bound` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/AxialAreaDensity.lean (declaration OAI.CubicTorus.isMinimizerAt_bottom_extent_calibration)

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

theorem isMinimizerAt_bottom_extent_calibration {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
    (hout : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun _ ↦ true))∉closure (openRepresentative E))
    (hin0 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==0))∈openRepresentative E)
    (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    0<H*s ∧ Real.pi*(1-s)≤((H/2)*s)^2 ∧
      ∃ L : ℝ,L∈Ioo 0 1 ∧
        (∀ y∈centeredAxialSlice (openRepresentative Eᶜ) (fun k ↦ !b k) i (octantHeight b i 0 : AxisCircle),2*‖y 1‖<L) ∧
        (1-s)/L+Real.pi*L/4≤(H/2)*s := by
  sorry

end CubicTorus

end
end

end

end OAI
end

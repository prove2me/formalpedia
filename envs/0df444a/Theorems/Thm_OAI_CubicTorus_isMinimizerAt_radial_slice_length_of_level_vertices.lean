-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_radial_slice_length_of_level_vertices
-- name    : OAI.CubicTorus.isMinimizerAt_radial_slice_length_of_level_vertices
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:09:23.543021+00:00
-- url     : https://prove2.me/theorems/01f539ea-d03c-4078-b560-1a352db503df
-- title:
--   OAI.CubicTorus.isMinimizerAt_radial_slice_length_of_level_vertices: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_radial_slice_length_of_level_vertices` of [lean/OAI/Geometry/CubicTorus/Estimates/MinimizerLevelSliceIsoperimetric.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/MinimizerLevelSliceIsoperimetric.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_radial_slice_length_of_level_vertices {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
--       {s : Fin 3 → Bool}
--       (hsg : ∀ (x : Cover) (i : Fin 3),
--         quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
--       {t : ℝ} (ht : t∈Icc (chamberCorner s 0) (chamberCorner s 0+1/2))
--       (hv1 : quotientMap (coordinateSectionPoint (chamberCorner s) t (1/2 : ℂ))∉closure (openRepresentative E))
--       (hv2 : quotientMap (coordinateSectionPoint (chamberCorner s) t ((1/2 : ℂ)*Complex.I))∉closure (openRepresentative E))
--       (htE : quotientMap (coordinateSectionPoint (chamberCorner s) t 0)∈openRepresentative E) :
--       ∃ r : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) r ∧ Function.Periodic r 1 ∧ (∀ a,0 < r a) ∧
--         axialSectionArea (openRepresentative E) 0 t=Real.pi*(∫ a in (0 : ℝ)..1,(r a)^2) ∧
--         axialSlicePerimeter (openRepresentative E) 0 t=
--           ENNReal.ofReal (∫ a in (0 : ℝ)..1,Real.sqrt ((deriv r a)^2+(2*Real.pi*r a)^2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.axialSectionArea`, `OAI.CubicTorus.axialSlicePerimeter`, `OAI.CubicTorus.chamberCorner`, `OAI.CubicTorus.coordinateHalf`, `OAI.CubicTorus.coordinateReflection`, `OAI.CubicTorus.coordinateSectionPoint` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_two_missing_vertices_top_flux` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/MinimizerLevelSliceIsoperimetric.lean (declaration OAI.CubicTorus.isMinimizerAt_radial_slice_length_of_level_vertices)

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

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_radial_slice_length_of_level_vertices {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {t : ℝ} (ht : t∈Icc (chamberCorner s 0) (chamberCorner s 0+1/2))
    (hv1 : quotientMap (coordinateSectionPoint (chamberCorner s) t (1/2 : ℂ))∉closure (openRepresentative E))
    (hv2 : quotientMap (coordinateSectionPoint (chamberCorner s) t ((1/2 : ℂ)*Complex.I))∉closure (openRepresentative E))
    (htE : quotientMap (coordinateSectionPoint (chamberCorner s) t 0)∈openRepresentative E) :
    ∃ r : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) r ∧ Function.Periodic r 1 ∧ (∀ a,0 < r a) ∧
      axialSectionArea (openRepresentative E) 0 t=Real.pi*(∫ a in (0 : ℝ)..1,(r a)^2) ∧
      axialSlicePerimeter (openRepresentative E) 0 t=
        ENNReal.ofReal (∫ a in (0 : ℝ)..1,Real.sqrt ((deriv r a)^2+(2*Real.pi*r a)^2)) := by
  sorry

end CubicTorus

end
end

end OAI
end

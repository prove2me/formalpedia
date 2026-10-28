-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_two_missing_vertices_top_flux
-- name    : OAI.CubicTorus.isMinimizerAt_two_missing_vertices_top_flux
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:14:19.220988+00:00
-- url     : https://prove2.me/theorems/c037177d-3c2f-4097-b563-bb078ba42839
-- title:
--   OAI.CubicTorus.isMinimizerAt_two_missing_vertices_top_flux: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_two_missing_vertices_top_flux` of [lean/OAI/Geometry/CubicTorus/Estimates/MinimizerLevelSliceIsoperimetric.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/MinimizerLevelSliceIsoperimetric.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_two_missing_vertices_top_flux {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
--       {s : Fin 3 → Bool}
--       (hsg : ∀ (x : Cover) (i : Fin 3),
--         quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
--       {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
--         H*directionalFlux E D.coordinate D.function)
--       (hv1 : quotientMap (chamberVertex s (fun j => decide (j=0 ∨ j=1)))∉openRepresentative E)
--       (hv2 : quotientMap (chamberVertex s (fun j => decide (j=0 ∨ j=2)))∉openRepresentative E) :
--       Real.sqrt (Real.pi*axialSectionArea (openRepresentative E) 0 (chamberCorner s 0+1/2))≤
--         ((μ.mass : ℝ)/2)*axialFluxWeight μ 0+
--           (H/2)*(axialSectionArea (openRepresentative E) 0 (chamberCorner s 0+1/2)-V)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.axialFluxWeight`, `OAI.CubicTorus.axialSectionArea`, `OAI.CubicTorus.chamberCorner`, `OAI.CubicTorus.chamberVertex`, `OAI.CubicTorus.coordinateHalf`, `OAI.CubicTorus.coordinateReflection`, `OAI.CubicTorus.directionalFlux`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.Periodic.Variation` and `OAI.CubicTorus.Periodic.normalFirstVariation` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI_CubicTorus_isMinimizerAt_first_transition_any_corner_excluded`, `OAI.CubicTorus.isMinimizerAt_four_corner_necessary_data`, `OAI_CubicTorus_isMinimizerAt_second_transition_standard` and `OAI_CubicTorus_isMinimizerAt_two_occupied_vertices_bottom_flux` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/MinimizerLevelSliceIsoperimetric.lean (declaration OAI.CubicTorus.isMinimizerAt_two_missing_vertices_top_flux)

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

theorem isMinimizerAt_two_missing_vertices_top_flux {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (hv1 : quotientMap (chamberVertex s (fun j => decide (j=0 ∨ j=1)))∉openRepresentative E)
    (hv2 : quotientMap (chamberVertex s (fun j => decide (j=0 ∨ j=2)))∉openRepresentative E) :
    Real.sqrt (Real.pi*axialSectionArea (openRepresentative E) 0 (chamberCorner s 0+1/2))≤
      ((μ.mass : ℝ)/2)*axialFluxWeight μ 0+
        (H/2)*(axialSectionArea (openRepresentative E) 0 (chamberCorner s 0+1/2)-V) := by
  sorry

end CubicTorus

end
end

end OAI
end

-- Prove2me | Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_H1_translation_jacobi
-- name    : OAI.CubicTorus.Periodic.isMinimizerAt_H1_translation_jacobi
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:26:38.26344+00:00
-- url     : https://prove2.me/theorems/30c0f9e2-5f7f-4878-9971-6cf3e47e877c
-- title:
--   OAI.CubicTorus.Periodic.isMinimizerAt_H1_translation_jacobi: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.Periodic.isMinimizerAt_H1_translation_jacobi` of [lean/OAI/Geometry/CubicTorus/Curvature/NormalCurvatureScalar.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Curvature/NormalCurvatureScalar.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus.Periodic`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_H1_translation_jacobi {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
--       ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover)
--         (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--         (hp : ∀ m x,N (x+latticeVector m)=N x),
--         IsNormalMeasure E μ ∧
--         (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
--         (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
--           (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
--             0 ≤ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
--         (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
--           0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
--         (∀ i : Fin 3,surfaceMean μ (surfaceSmoothJet μ (normalComponentScalar N hN hp i))=0 ∧
--           ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
--             (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0) ∧
--         (∀ (u : SurfaceJet μ),u∈surfaceH1 μ → surfaceMean μ u=0 →
--           surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u=0 →
--           ∀ U : Set Torus,IsOpen U → (U∩frontier (openRepresentative E)).Nonempty →
--           (∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0) →
--           ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u w=0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.SurfaceJet`, `OAI.CubicTorus.coverTrace`, `OAI.CubicTorus.normalComponentScalar`, `OAI.CubicTorus.normalProjection`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.smoothPeriodicScalars`, `OAI.CubicTorus.surfaceCurvatureLp`, `OAI.CubicTorus.surfaceJacobiB` and `OAI.CubicTorus.surfaceSmoothJet` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.surfaceH1` and `OAI.CubicTorus.surfaceMean` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.divergence`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.Periodic.isMinimizerAt_translation_nodal_count`, `OAI.CubicTorus.isMinimizerAt_axis_strict_normal_sign`, `OAI.CubicTorus.isMinimizerAt_corner_boundary_heights_null`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_flux_unrestricted`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_projection`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_sharp_area_flux`, `OAI.CubicTorus.isMinimizerAt_nesting_cubic_gain`, `OAI.CubicTorus.isMinimizerAt_nonstandard_strict_octant`, `OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign` and `OAI.CubicTorus.isMinimizerAt_three_vertex_bottom` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Curvature/NormalCurvatureScalar.lean (declaration OAI.CubicTorus.Periodic.isMinimizerAt_H1_translation_jacobi)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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
namespace Periodic

theorem isMinimizerAt_H1_translation_jacobi {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N)
      (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
          0 ≤ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
      (∀ i : Fin 3,surfaceMean μ (surfaceSmoothJet μ (normalComponentScalar N hN hp i))=0 ∧
        ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
          (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0) ∧
      (∀ (u : SurfaceJet μ),u∈surfaceH1 μ → surfaceMean μ u=0 →
        surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u=0 →
        ∀ U : Set Torus,IsOpen U → (U∩frontier (openRepresentative E)).Nonempty →
        (∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0) →
        ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u w=0) := by
  sorry

end Periodic
end CubicTorus

end
end

end

end OAI
end

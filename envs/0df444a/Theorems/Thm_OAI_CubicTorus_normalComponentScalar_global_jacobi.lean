-- Prove2me | Theorems.Thm_OAI_CubicTorus_normalComponentScalar_global_jacobi
-- name    : OAI.CubicTorus.normalComponentScalar_global_jacobi
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:38:59.397849+00:00
-- url     : https://prove2.me/theorems/5314031f-5bfa-41c6-9ccf-074630e84f77
-- title:
--   OAI.CubicTorus.normalComponentScalar_global_jacobi: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.normalComponentScalar_global_jacobi` of [lean/OAI/Geometry/CubicTorus/Curvature/NormalCurvatureScalar.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Curvature/NormalCurvatureScalar.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem normalComponentScalar_global_jacobi {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∀ᶠ y in 𝓝 x,‖N y‖=1)
--       (hs : ∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
--         0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) (i : Fin 3) :
--       ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
--         (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.SurfaceJet`, `OAI.CubicTorus.normalComponentScalar`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.smoothPeriodicScalars`, `OAI.CubicTorus.surfaceCurvatureLp`, `OAI.CubicTorus.surfaceJacobiB` and `OAI.CubicTorus.surfaceSmoothJet` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.surfaceH1` and `OAI.CubicTorus.surfaceMean` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.Periodic.isMinimizerAt_H1_translation_jacobi`, `OAI.CubicTorus.Periodic.isMinimizerAt_full_jacobi_system`, `OAI_CubicTorus_isMinimizerAt_missing_neighbor_area_flux`, `OAI_CubicTorus_isMinimizerAt_nonstandard_strict_signs_of_actual_normal` and `OAI_CubicTorus_isMinimizerAt_normal_strong_minimum` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Curvature/NormalCurvatureScalar.lean (declaration OAI.CubicTorus.normalComponentScalar_global_jacobi)

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

theorem normalComponentScalar_global_jacobi {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∀ᶠ y in 𝓝 x,‖N y‖=1)
    (hs : ∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
      0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) (i : Fin 3) :
    ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0 := by
  sorry

end CubicTorus

end
end

end

end OAI
end

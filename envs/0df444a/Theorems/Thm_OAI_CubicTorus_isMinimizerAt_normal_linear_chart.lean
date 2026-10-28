-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_normal_linear_chart
-- name    : OAI.CubicTorus.isMinimizerAt_normal_linear_chart
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:07:35.562208+00:00
-- url     : https://prove2.me/theorems/3cd18072-2008-4697-98b8-b47f84275611
-- title:
--   OAI.CubicTorus.isMinimizerAt_normal_linear_chart: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_normal_linear_chart` of [lean/OAI/Geometry/CubicTorus/Curvature/CMCFrameOperator.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Curvature/CMCFrameOperator.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_normal_linear_chart {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
--       ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
--         ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
--         (∀ᶠ y in 𝓝 (0 : Plane),N (x+normalGraph n f y)=σ • graphSlopeNormal n (gradient f y) ∧
--           quotientMap (x+normalGraph n f y)∈frontier (openRepresentative E)) ∧
--         (∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈frontier (openRepresentative E) ↔
--           normalGraph n f (normalPlaneCoordinates n v)=v) ∧
--         ∃ r : ℝ,0 < r ∧ (∀ y∈Metric.ball (0 : Plane) r,‖gradient f y‖≤1) ∧
--           ∀ i : Fin 2,LinearCMCEquation
--             (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) (gradient f)
--             (fun _ => 0) (Metric.ball 0 r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.LinearCMCEquation`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.Plane`, `OAI.CubicTorus.graphSlopeNormal`, `OAI.CubicTorus.normalGraph`, `OAI.CubicTorus.normalPlaneCoordinates` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_axial_local_cylinder`, `OAI_CubicTorus_isMinimizerAt_exists_coordinate_symmetries_measurable`, `OAI.CubicTorus.isMinimizerAt_nodal_splice_closed`, `OAI.CubicTorus.isMinimizerAt_normal_coordinate_strict_or_zero`, `OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor` and `OAI.CubicTorus.isMinimizerAt_zero_coordinate_cylindrical` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Curvature/CMCFrameOperator.lean (declaration OAI.CubicTorus.isMinimizerAt_normal_linear_chart)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

theorem isMinimizerAt_normal_linear_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),N (x+normalGraph n f y)=σ • graphSlopeNormal n (gradient f y) ∧
        quotientMap (x+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      (∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v) ∧
      ∃ r : ℝ,0 < r ∧ (∀ y∈Metric.ball (0 : Plane) r,‖gradient f y‖≤1) ∧
        ∀ i : Fin 2,LinearCMCEquation
          (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) (gradient f)
          (fun _ => 0) (Metric.ball 0 r) := by
  sorry

end CubicTorus

end
end

end OAI
end

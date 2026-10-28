-- Prove2me | Theorems.Thm_OAI_CubicTorus_surfaceH1_jacobi_graph_smoothAt
-- name    : OAI.CubicTorus.surfaceH1_jacobi_graph_smoothAt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:40:31.759468+00:00
-- url     : https://prove2.me/theorems/3ab6df9d-636a-494c-a580-9f5733cd2d66
-- title:
--   OAI.CubicTorus.surfaceH1_jacobi_graph_smoothAt: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.surfaceH1_jacobi_graph_smoothAt` of [lean/OAI/Geometry/CubicTorus/Regularity/SurfaceNormalReverse.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/SurfaceNormalReverse.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem surfaceH1_jacobi_graph_smoothAt
--       (μ : FiniteMeasure NormalBundle) (q : Lp ℝ ∞ (μ : Measure NormalBundle))
--       {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
--       (hhom : ∀ z∈surfaceH1 μ, surfaceJacobiB μ q u z=0)
--       (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} {K : ℝ≥0}
--       (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
--       {φ : Cover → ℝ} (hφ : Measurable φ) (hφb : ∀ x, φ x∈Icc 0 1)
--       (hφO : tsupport φ ⊆ {x | ∀ i, 0<x i ∧ x i<1})
--       (hm : (μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (φ z.1)) =
--         Measure.map (actualNormalGraphChart a hn g)
--           (volume.withDensity (fun y => ENNReal.ofReal
--             (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
--       {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
--       (hχO : tsupport χ ⊆ {x | ∀ i, 0<x i ∧ x i<1})
--       (hφχ : ∀ x∈tsupport χ, φ x=1)
--       {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
--       (hunit : ∀ y∈Metric.ball (0 : Plane) R, χ (a+normalGraph n g y)=1)
--       {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖≤1)
--       (hpc : ContDiffAt ℝ (⊤ : ℕ∞) p 0)
--       (hpe : ∀ y∈Metric.ball (0 : Plane) R, p y=gradient g y)
--       (hHolder : ∀ x∈Metric.ball (0 : Plane) R, ∀ y∈Metric.ball (0 : Plane) R,
--         ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
--       (hlin : ∀ i : Fin 2, LinearCMCEquation
--         (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
--         (fun _ => 0) (Metric.ball 0 R))
--       (hqp : (fun y => q (actualNormalGraphChart a hn g y))
--         =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] graphSquaredSecondFundamentalForm g)
--       {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
--       (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
--         fun y => u.1 (actualNormalGraphChart a hn g y)) :
--       ContDiffAt ℝ (⊤ : ℕ∞) f 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.LinearCMCEquation`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.Plane`, `OAI.CubicTorus.SurfaceJet`, `OAI.CubicTorus.actualNormalGraphChart`, `OAI.CubicTorus.cmcJacobian`, `OAI.CubicTorus.graphAreaVector`, `OAI.CubicTorus.graphSquaredSecondFundamentalForm`, `OAI.CubicTorus.normalGraph` and `OAI.CubicTorus.surfaceJacobiB` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.surfaceH1` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.normalMeasure_H1_jacobi_signed_graph_smoothAt` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/SurfaceNormalReverse.lean (declaration OAI.CubicTorus.surfaceH1_jacobi_graph_smoothAt)

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

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceH1_jacobi_graph_smoothAt
    (μ : FiniteMeasure NormalBundle) (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ, surfaceJacobiB μ q u z=0)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} {K : ℝ≥0}
    (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {φ : Cover → ℝ} (hφ : Measurable φ) (hφb : ∀ x, φ x∈Icc 0 1)
    (hφO : tsupport φ ⊆ {x | ∀ i, 0<x i ∧ x i<1})
    (hm : (μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ {x | ∀ i, 0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ, φ x=1)
    {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hunit : ∀ y∈Metric.ball (0 : Plane) R, χ (a+normalGraph n g y)=1)
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖≤1)
    (hpc : ContDiffAt ℝ (⊤ : ℕ∞) p 0)
    (hpe : ∀ y∈Metric.ball (0 : Plane) R, p y=gradient g y)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R, ∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (hlin : ∀ i : Fin 2, LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 R))
    (hqp : (fun y => q (actualNormalGraphChart a hn g y))
      =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] graphSquaredSecondFundamentalForm g)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
      fun y => u.1 (actualNormalGraphChart a hn g y)) :
    ContDiffAt ℝ (⊤ : ℕ∞) f 0 := by
  sorry

end CubicTorus

end
end

end OAI
end

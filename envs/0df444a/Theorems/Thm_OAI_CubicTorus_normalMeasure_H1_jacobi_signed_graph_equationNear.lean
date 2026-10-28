-- Prove2me | Theorems.Thm_OAI_CubicTorus_normalMeasure_H1_jacobi_signed_graph_equationNear
-- name    : OAI.CubicTorus.normalMeasure_H1_jacobi_signed_graph_equationNear
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:39:26.038051+00:00
-- url     : https://prove2.me/theorems/0c132c6c-d19a-4ece-ac65-02be2de73fb3
-- title:
--   OAI.CubicTorus.normalMeasure_H1_jacobi_signed_graph_equationNear: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.normalMeasure_H1_jacobi_signed_graph_equationNear` of [lean/OAI/Geometry/CubicTorus/Regularity/NormalRotationWeak.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/NormalRotationWeak.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem normalMeasure_H1_jacobi_signed_graph_equationNear {E : Set Torus} (hE : MeasurableSet E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
--       (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
--       {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
--       {g : Plane → ℝ} {K : ℝ≥0} (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
--       (hgraph : (∀ᵐ x : Cover ∂volume,x∈U →
--         (quotientMap x∈E ↔ graphSignedHeight a n g x<0)) ∨
--         (∀ᵐ x : Cover ∂volume,x∈U →
--         (quotientMap x∈E ↔ 0<graphSignedHeight a n g x)))
--       {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
--       (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
--       {R : ℝ} (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1)
--       {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsχ : HasCompactSupport χ)
--       (hχO : tsupport χ⊆{x | ∀ i,0<x i ∧ x i<1})
--       (hφχ : ∀ x∈tsupport χ,φ x=1)
--       {s D : ℝ} (hs : 0 < s) (hD : 0≤D)
--       (hunit : ∀ y∈Metric.ball (0 : Plane) s,χ (a+normalGraph n g y)=1)
--       {p : Plane → Plane} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hpb : ∀ y,‖p y‖≤1)
--       (hpe : EqOn p (gradient g) (Metric.ball 0 s))
--       (hpD : ∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y)
--       (hlin : ∀ i : Fin 2,LinearCMCEquation
--         (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
--         (fun _ => 0) (Metric.ball 0 s))
--       (hNu : ∀ y∈Metric.ball (0 : Plane) s,∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1)
--       {S : Set Torus} {F : Torus → ℝ} (hF : ContinuousOn F S)
--       (hS : ∀ y∈Metric.ball (0 : Plane) s,quotientMap (a+normalGraph n g y)∈S)
--       (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
--       LinearCMCEquationNear (fun y => cmcWeight (gradient g y)*
--         F (quotientMap (a+normalGraph n g y))) (gradient g) (fun _ => 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.LinearCMCEquation`, `OAI.CubicTorus.LinearCMCEquationNear`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.Plane`, `OAI.CubicTorus.SurfaceJet`, `OAI.CubicTorus.cmcJacobian`, `OAI.CubicTorus.cmcWeight`, `OAI.CubicTorus.graphSignedHeight`, `OAI.CubicTorus.normalGraph`, `OAI.CubicTorus.normalProjection`, `OAI.CubicTorus.surfaceCurvatureLp` and `OAI.CubicTorus.surfaceJacobiB` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.surfaceH1` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_H1_jacobi_unique_continuation` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/NormalRotationWeak.lean (declaration OAI.CubicTorus.normalMeasure_H1_jacobi_signed_graph_equationNear)

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

theorem normalMeasure_H1_jacobi_signed_graph_equationNear {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgraph : (∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ graphSignedHeight a n g x<0)) ∨
      (∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ 0<graphSignedHeight a n g x)))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    {R : ℝ} (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsχ : HasCompactSupport χ)
    (hχO : tsupport χ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ,φ x=1)
    {s D : ℝ} (hs : 0 < s) (hD : 0≤D)
    (hunit : ∀ y∈Metric.ball (0 : Plane) s,χ (a+normalGraph n g y)=1)
    {p : Plane → Plane} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hpb : ∀ y,‖p y‖≤1)
    (hpe : EqOn p (gradient g) (Metric.ball 0 s))
    (hpD : ∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y)
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 s))
    (hNu : ∀ y∈Metric.ball (0 : Plane) s,∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1)
    {S : Set Torus} {F : Torus → ℝ} (hF : ContinuousOn F S)
    (hS : ∀ y∈Metric.ball (0 : Plane) s,quotientMap (a+normalGraph n g y)∈S)
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
    LinearCMCEquationNear (fun y => cmcWeight (gradient g y)*
      F (quotientMap (a+normalGraph n g y))) (gradient g) (fun _ => 0) := by
  sorry

end CubicTorus

end
end

end OAI
end

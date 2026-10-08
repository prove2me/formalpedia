-- Prove2me | Theorems.Thm_MifflinSemismooth_Composition_prop1_c
-- name    : MifflinSemismooth.Composition.prop1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:38.01112+00:00
-- url     : https://prove2.me/theorems/c8d852bf-cf72-4f6a-b884-2d9783409fb6
-- title:
--   Proposition 1(c) — almost-everywhere differentiability and gradient-limit formula
-- statement:
--   If $F$ is Lipschitz on an open set $B$ and $x\in B$, then $F$ is differentiable almost everywhere in $B$. Moreover,
--
--   $$\partial F(x)=\operatorname{conv}\left\{\lim_{k\to\infty}\nabla F(x_k):x_k\in B,\ x_k\to x,\ F\text{ differentiable at every }x_k\right\}. $$
--
--   This identifies the paper's support-set generalized gradient with the convex hull of limiting ordinary gradients.
--
--   **Formalization Note** The points $x_k$ must be differentiability points; Mathlib's total `gradient` otherwise returns a default value. The almost-everywhere qualifier uses Lebesgue volume on Euclidean space.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 3, Proposition 1(c)

import Mathlib
import Definitions.Def_MifflinSemismooth_Extremal_Basic

open Filter Topology MeasureTheory

namespace MifflinSemismooth.Composition

theorem prop1_c {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : Set (EuclideanSpace ℝ (Fin n))) (hB : IsOpen B)
    (K : NNReal) (hFB : LipschitzOnWith K F B)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ B) :
    (∀ᵐ y ∂(MeasureTheory.volume), y ∈ B → DifferentiableAt ℝ F y) ∧
      MifflinSemismooth.Extremal.genGrad F x = convexHull ℝ
        {g | ∃ xs : ℕ → EuclideanSpace ℝ (Fin n),
          (∀ k, xs k ∈ B) ∧
          (∀ k, DifferentiableAt ℝ F (xs k)) ∧
          Tendsto xs atTop (𝓝 x) ∧
          Tendsto (fun k => gradient F (xs k)) atTop (𝓝 g)} := by sorry

end MifflinSemismooth.Composition

-- Prove2me | Theorems.Thm_GradErrors_Deterministic_descent_inequality
-- name    : GradErrors.Deterministic.descent_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:29:31.291622+00:00
-- url     : https://prove2.me/theorems/49cda071-e828-4ff5-8bac-3e703d5e0ce7
-- title:
--   (2.4), p. 630 — descent inequality f(x + z) ≤ f(x) + z′∇f(x) + (L/2)‖z‖² for an L-Lipschitz gradient
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable and suppose its gradient is Lipschitz continuous with constant $L\ge 0$:
--   $$\|\nabla f(x)-\nabla f(\bar x)\|\le L\|x-\bar x\|\qquad\forall x,\bar x\in\mathbb R^n.$$
--   Then for all vectors $x,z\in\mathbb R^n$,
--   $$f(x+z)\le f(x)+z'\nabla f(x)+\frac L2\|z\|^2.$$
--
--   This quadratic upper bound (the "descent lemma") is the first step in the proof of Proposition 1: applied with $x=x_t$ and $z=\gamma_t(s_t+w_t)$ it bounds $f(x_{t+1})$ in terms of $f(x_t)$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $x'y$ is the real inner product and $\nabla f$ is Mathlib's `gradient f` (the true gradient, since `ContDiff ℝ 1 f` is assumed). The Lipschitz constant is taken as `L : ℝ≥0` with `LipschitzWith L (gradient f)`; this is equivalent to (2.1) for some real constant $L$.
-- source:
--   Bertsekas and Tsitsiklis, Gradient Convergence in Gradient Methods with Errors, SIAM J. Optim. 10 (2000), https://doi.org/10.1137/S1052623497331063, p. 630, §2, proof of Proposition 1, display (2.4) (first and last members of the chain)

import Mathlib

open Filter Topology NNReal InnerProductSpace

namespace GradErrors.Deterministic

theorem descent_inequality {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f)) (x z : EuclideanSpace ℝ (Fin n)) :
    f (x + z) ≤ f x + ⟪z, gradient f x⟫_ℝ + (L : ℝ) / 2 * ‖z‖ ^ 2 := by sorry

end GradErrors.Deterministic

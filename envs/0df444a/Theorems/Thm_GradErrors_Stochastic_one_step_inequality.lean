-- Prove2me | Theorems.Thm_GradErrors_Stochastic_one_step_inequality
-- name    : GradErrors.Stochastic.one_step_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:18:02.371718+00:00
-- url     : https://prove2.me/theorems/c4c1705a-6c69-4a5b-be55-9b06f0cd1dc3
-- title:
--   (4.4), p. 636 — one-step inequality f(x + γ(s + w)) ≤ f(x) − γ(c₁/2)‖∇f(x)‖² + γ∇f(x)′w + γ²2Lc₂² + γ²L‖w‖² when γ2Lc₂² ≤ c₁/2
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable with an $L$-Lipschitz gradient,
--   $$\|\nabla f(x)-\nabla f(\bar x)\|\le L\|x-\bar x\|\qquad\forall x,\bar x\in\mathbb R^n .$$
--   Fix vectors $x,s,w\in\mathbb R^n$ and scalars $\gamma>0$, $c_1>0$, $c_2>0$ such that the direction $s$ satisfies the descent conditions (4.1) at $x$,
--   $$c_1\|\nabla f(x)\|^2\le-\nabla f(x)'s,\qquad \|s\|\le c_2\bigl(1+\|\nabla f(x)\|\bigr),$$
--   and such that the stepsize is small enough: $\gamma\,2Lc_2^2\le c_1/2$. Then, for the step $x+\gamma(s+w)$ with an arbitrary error vector $w$,
--   $$f\bigl(x+\gamma(s+w)\bigr)\le f(x)-\gamma\frac{c_1}{2}\|\nabla f(x)\|^2+\gamma\,\nabla f(x)'w+\gamma^2\,2Lc_2^2+\gamma^2L\|w\|^2 .$$
--
--   This is the pathwise descent estimate (4.4) on which the proof of Proposition 3 rests: applied with $x=x_t$, $s=s_t$, $w=w_t$ and $\gamma=\gamma_t$ it bounds $f(x_{t+1})$ by $f(x_t)$, a decrease proportional to $\gamma_t\|\nabla f(x_t)\|^2$, a zero-mean noise term $\gamma_t\nabla f(x_t)'w_t$, and second-order terms. No probability is involved: the inequality holds for every vector $w$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $x'y$ is the real inner product and $\nabla f$ is Mathlib's `gradient f`. The Lipschitz constant is `L : ℝ≥0` with `LipschitzWith L (gradient f)`, equivalent to (2.1) for some real constant $L$. The stepsize condition $\gamma\,2Lc_2^2\le c_1/2$ is the page's own validity condition for the last inequality of (4.4) ("valid only when $t$ is large enough so that $\gamma_t2Lc_2^2\le c_1/2$"); it is a hypothesis here. Only the first and last members of the chain (4.4) are stated.
-- source:
--   Bertsekas and Tsitsiklis, Gradient Convergence in Gradient Methods with Errors, SIAM J. Optim. 10 (2000), https://doi.org/10.1137/S1052623497331063, p. 636, §4, proof of Proposition 3, display (4.4) (first and last members of the chain, with the validity condition stated after it)

import Mathlib

open Filter Topology NNReal ENNReal MeasureTheory ProbabilityTheory InnerProductSpace

namespace GradErrors.Stochastic

theorem one_step_inequality {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f)) (x s w : EuclideanSpace ℝ (Fin n))
    (γ c₁ c₂ : ℝ) (hγ : 0 < γ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h41a : c₁ * ‖gradient f x‖ ^ 2 ≤ -⟪gradient f x, s⟫_ℝ)
    (h41b : ‖s‖ ≤ c₂ * (1 + ‖gradient f x‖))
    (hγsmall : γ * (2 * (L : ℝ) * c₂ ^ 2) ≤ c₁ / 2) :
    f (x + γ • (s + w)) ≤ f x - γ * (c₁ / 2) * ‖gradient f x‖ ^ 2 + γ * ⟪gradient f x, w⟫_ℝ
      + γ ^ 2 * (2 * (L : ℝ) * c₂ ^ 2) + γ ^ 2 * (L : ℝ) * ‖w‖ ^ 2 := by sorry

end GradErrors.Stochastic

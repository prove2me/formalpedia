-- Prove2me | Theorems.Thm_GradErrors_Deterministic_liminf_grad_eq_zero
-- name    : GradErrors.Deterministic.liminf_grad_eq_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:30:08.436906+00:00
-- url     : https://prove2.me/theorems/d9a748a0-b7b4-490e-97ff-b69bd2484bfa
-- title:
--   §2, p. 631, after (2.6) — if f(x_t) does not tend to −∞, then lim inf ‖∇f(x_t)‖ = 0
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable with $L$-Lipschitz gradient, $\|\nabla f(x)-\nabla f(\bar x)\|\le L\|x-\bar x\|$ for all $x,\bar x$ (standing assumption (2.1) of the paper). Let $x_t, s_t, w_t\in\mathbb R^n$ and $\gamma_t\in\mathbb R$ ($t=0,1,\dots$) satisfy the recursion
--   $$x_{t+1}=x_t+\gamma_t(s_t+w_t),$$
--   where, for positive constants $c_1,c_2,p,q$ and every $t$,
--   1. (descent direction, (2.2)) $c_1\|\nabla f(x_t)\|^2\le-\nabla f(x_t)'s_t$ and $\|s_t\|\le c_2\bigl(1+\|\nabla f(x_t)\|\bigr)$;
--   2. (error bound, (2.3)) $\|w_t\|\le\gamma_t\bigl(q+p\|\nabla f(x_t)\|\bigr)$;
--   3. (stepsizes) $\gamma_t>0$, $\sum_{t=0}^\infty\gamma_t=\infty$ and $\sum_{t=0}^\infty\gamma_t^2<\infty$.
--
--   If $f(x_t)$ does not tend to $-\infty$, then
--   $$\liminf_{t\to\infty}\|\nabla f(x_t)\|=0,$$
--   that is, for every $\epsilon>0$ there are infinitely many $t$ with $\|\nabla f(x_t)\|<\epsilon$.
--
--   In the proof of Proposition 1 this is the step between (2.6) and the full convergence $\nabla f(x_t)\to 0$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $x'y$ is the real inner product and $\nabla f$ is Mathlib's `gradient f` (the true gradient, since `ContDiff ℝ 1 f` is assumed). The Lipschitz constant is taken as `L : ℝ≥0` with `LipschitzWith L (gradient f)`; this is equivalent to (2.1) for some real constant $L$. $x_t, s_t, w_t$ are arbitrary sequences: nothing about how they are produced is assumed beyond (2.2)–(2.3). The lim inf is written out as "for every $\epsilon>0$, $\|\nabla f(x_t)\|<\epsilon$ frequently", not as Lean's `liminf`, which takes a junk value on sequences that are not bounded. The page states the claim in the branch where $f(x_t)$ converges; by (2.6) that branch is exactly the negation of $f(x_t)\to-\infty$.
-- source:
--   Bertsekas and Tsitsiklis, Gradient Convergence in Gradient Methods with Errors, SIAM J. Optim. 10 (2000), https://doi.org/10.1137/S1052623497331063, p. 631, §2, proof of Proposition 1, the paragraph after (2.6)

import Mathlib

open Filter Topology NNReal InnerProductSpace

namespace GradErrors.Deterministic

theorem liminf_grad_eq_zero {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f))
    (x s w : ℕ → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ)
    (c₁ c₂ p q : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hp : 0 < p) (hq : 0 < q)
    (hx : ∀ t, x (t + 1) = x t + γ t • (s t + w t))
    (h22a : ∀ t, c₁ * ‖gradient f (x t)‖ ^ 2 ≤ -⟪gradient f (x t), s t⟫_ℝ)
    (h22b : ∀ t, ‖s t‖ ≤ c₂ * (1 + ‖gradient f (x t)‖))
    (h23 : ∀ t, ‖w t‖ ≤ γ t * (q + p * ‖gradient f (x t)‖))
    (hγ : ∀ t, 0 < γ t)
    (hsum : Tendsto (fun T => ∑ t ∈ Finset.range T, γ t) atTop atTop)
    (hsq : Summable (fun t => γ t ^ 2)) :
    ¬ Tendsto (fun t => f (x t)) atTop atBot →
      ∀ ε > 0, ∃ᶠ t in atTop, ‖gradient f (x t)‖ < ε := by sorry

end GradErrors.Deterministic

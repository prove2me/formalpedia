-- Prove2me | Theorems.Thm_GradErrors_Deterministic_eventual_descent
-- name    : GradErrors.Deterministic.eventual_descent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:29:42.715691+00:00
-- url     : https://prove2.me/theorems/84cd40ce-7d08-4343-8901-f81139d00c8a
-- title:
--   (2.5), p. 631 — eventually f(x_{t+1}) ≤ f(x_t) − γ_t β₁‖∇f(x_t)‖² + γ_t² β₂ for some positive β₁, β₂
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable with $L$-Lipschitz gradient, $\|\nabla f(x)-\nabla f(\bar x)\|\le L\|x-\bar x\|$ for all $x,\bar x$ (standing assumption (2.1) of the paper). Let $x_t, s_t, w_t\in\mathbb R^n$ and $\gamma_t\in\mathbb R$ ($t=0,1,\dots$) satisfy the recursion
--   $$x_{t+1}=x_t+\gamma_t(s_t+w_t),$$
--   where, for positive constants $c_1,c_2,p,q$ and every $t$,
--   1. (descent direction, (2.2)) $c_1\|\nabla f(x_t)\|^2\le-\nabla f(x_t)'s_t$ and $\|s_t\|\le c_2\bigl(1+\|\nabla f(x_t)\|\bigr)$;
--   2. (error bound, (2.3)) $\|w_t\|\le\gamma_t\bigl(q+p\|\nabla f(x_t)\|\bigr)$;
--   3. (stepsizes) $\gamma_t>0$, $\sum_{t=0}^\infty\gamma_t=\infty$, and $\sum_{t=0}^\infty\gamma_t^2<\infty$.
--
--   Then there exist positive scalars $\beta_1,\beta_2$ and an index $T$ such that for all $t\ge T$
--   $$f(x_{t+1})\le f(x_t)-\gamma_t\beta_1\|\nabla f(x_t)\|^2+\gamma_t^2\beta_2.$$
--
--   This is the one-step descent estimate of the proof of Proposition 1; combined with Lemma 1 it yields (2.6).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $x'y$ is the real inner product and $\nabla f$ is Mathlib's `gradient f` (the true gradient, since `ContDiff ℝ 1 f` is assumed). The Lipschitz constant is taken as `L : ℝ≥0` with `LipschitzWith L (gradient f)`; this is equivalent to (2.1) for some real constant $L$. $x_t, s_t, w_t$ are arbitrary sequences: nothing about how they are produced is assumed beyond (2.2)–(2.3). The constants $\beta_1,\beta_2$ and the threshold $T$ are existential, as on the page ("for sufficiently large $t$ … where $\beta_1$ and $\beta_2$ are some positive scalars"). The divergent stepsize sum is retained from Proposition 1's setting, although the estimate itself uses only $\gamma_t\to 0$.
-- source:
--   Bertsekas and Tsitsiklis, Gradient Convergence in Gradient Methods with Errors, SIAM J. Optim. 10 (2000), https://doi.org/10.1137/S1052623497331063, p. 631, §2, proof of Proposition 1, display (2.5)

import Mathlib

open Filter Topology NNReal InnerProductSpace

namespace GradErrors.Deterministic

theorem eventual_descent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
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
    ∃ β₁ : ℝ, 0 < β₁ ∧ ∃ β₂ : ℝ, 0 < β₂ ∧ ∃ T : ℕ, ∀ t ≥ T,
      f (x (t + 1)) ≤ f (x t) - γ t * β₁ * ‖gradient f (x t)‖ ^ 2 + γ t ^ 2 * β₂ := by sorry

end GradErrors.Deterministic

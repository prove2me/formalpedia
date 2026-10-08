-- Prove2me | Theorems.Thm_GradErrors_Deterministic_proposition_1
-- name    : GradErrors.Deterministic.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:30:10.354075+00:00
-- url     : https://prove2.me/theorems/a17af7cb-1a1d-4743-b1ed-59b69351b6f6
-- title:
--   Proposition 1, p. 630 — gradient method with stepsize-proportional errors: f(x_t) → −∞, or f(x_t) converges and ∇f(x_t) → 0
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable with $L$-Lipschitz gradient, $\|\nabla f(x)-\nabla f(\bar x)\|\le L\|x-\bar x\|$ for all $x,\bar x$ (standing assumption (2.1) of the paper). Let $x_t, s_t, w_t\in\mathbb R^n$ and $\gamma_t\in\mathbb R$ ($t=0,1,\dots$) satisfy the recursion
--   $$x_{t+1}=x_t+\gamma_t(s_t+w_t),$$
--   where, for positive constants $c_1,c_2,p,q$ and every $t$,
--   1. (descent direction, (2.2)) $c_1\|\nabla f(x_t)\|^2\le-\nabla f(x_t)'s_t$ and $\|s_t\|\le c_2\bigl(1+\|\nabla f(x_t)\|\bigr)$;
--   2. (error bound, (2.3)) $\|w_t\|\le\gamma_t\bigl(q+p\|\nabla f(x_t)\|\bigr)$;
--   3. (stepsizes) $\gamma_t>0$, with
--   $$\sum_{t=0}^\infty\gamma_t=\infty,\qquad\sum_{t=0}^\infty\gamma_t^2<\infty.$$
--
--   Then either $f(x_t)\to-\infty$, or else $f(x_t)$ converges to a finite value and $\lim_{t\to\infty}\nabla f(x_t)=0$. Furthermore, every limit point $\bar x$ of $(x_t)$ is a stationary point of $f$: $\nabla f(\bar x)=0$.
--
--   This is the main deterministic result of the paper. It needs no boundedness of the iterates and no lower bound on $f$, and it allows a descent direction $s_t$ that is not the negative gradient together with an error $w_t$ whose size is proportional to the stepsize. It covers, for example, the incremental gradient method (Proposition 2 of the paper).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $x'y$ is the real inner product and $\nabla f$ is Mathlib's `gradient f` (the true gradient, since `ContDiff ℝ 1 f` is assumed). The Lipschitz constant is taken as `L : ℝ≥0` with `LipschitzWith L (gradient f)`; this is equivalent to (2.1) for some real constant $L$. $x_t, s_t, w_t$ are arbitrary sequences: nothing about how they are produced is assumed beyond (2.2)–(2.3). "Every limit point is stationary" is stated outside the disjunction, as on the page; a limit point is a cluster point of the sequence (`MapClusterPt xbar atTop x`). $\sum_t\gamma_t=\infty$ is divergence of the partial sums to $+\infty$, and $\sum_t\gamma_t^2<\infty$ is `Summable` of the nonnegative terms $\gamma_t^2$.
-- source:
--   Bertsekas and Tsitsiklis, Gradient Convergence in Gradient Methods with Errors, SIAM J. Optim. 10 (2000), https://doi.org/10.1137/S1052623497331063, p. 630, Proposition 1

import Mathlib

open Filter Topology NNReal InnerProductSpace

namespace GradErrors.Deterministic

theorem proposition_1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
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
    (Tendsto (fun t => f (x t)) atTop atBot ∨
      ((∃ l : ℝ, Tendsto (fun t => f (x t)) atTop (𝓝 l)) ∧
        Tendsto (fun t => gradient f (x t)) atTop (𝓝 0))) ∧
    ∀ xbar, MapClusterPt xbar atTop x → gradient f xbar = 0 := by sorry

end GradErrors.Deterministic

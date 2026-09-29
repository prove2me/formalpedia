-- Prove2me | Theorems.Thm_LogRegretOCO_OGD_strong_convexity_lower_bound
-- name    : LogRegretOCO.OGD.strong_convexity_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:32:39.165323+00:00
-- url     : https://prove2.me/theorems/ac222e47-3e38-4bc5-9f7a-4cfde3ed8e9e
-- title:
--   Eq. (1) — 2(f(x) − f(y)) ≤ 2∇f(x)ᵀ(x − y) − H‖y − x‖² for H-strongly convex f
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^n$ be convex, let $H\in\mathbb R$, and let $f:\mathbb R^n\to\mathbb R$ be $H$-strongly convex on $\mathcal P$: twice differentiable at the points of $\mathcal P$ with $\nabla^2 f(z)\succeq H I_n$ for every $z\in\mathcal P$. Then for all $x,y\in\mathcal P$,
--   $$2\bigl(f(x)-f(y)\bigr)\ \le\ 2\,\nabla f(x)^\top(x-y)\;-\;H\,\|y-x\|_2^2 .$$
--
--   This is the curvature inequality (1) in the proof of Theorem 1, used there with $x=x_t$, $y=x^*$ and $f=f_t$: strong convexity makes each round's loss relative to the comparator smaller than the linearised loss by a quadratic term, which is what cancels the telescoping distance terms.
--
--   **Formalization Note** The inequality is stated without $H>0$ (it holds for every real $H$ satisfying the Hessian bound); the paper's $H>0$ only enters Theorem 1. Points are `EuclideanSpace ℝ (Fin n)`, $\nabla f$ is Mathlib's `gradient`, and the inner product is `inner ℝ`.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 175, proof of Theorem 1, Eq. (1)

import Mathlib
import Definitions.Def_LogRegretOCO_OGD_Model

namespace LogRegretOCO.OGD

/-- **Eq. (1)** (p. 175): for an `H`-strongly convex `f` on a convex set `P` and `x, y ∈ P`,
`2 (f x − f y) ≤ 2 ∇f(x)ᵀ(x − y) − H ‖y − x‖²`. -/
theorem strong_convexity_lower_bound {n : ℕ} (P : Set (E n)) (hPc : Convex ℝ P) (H : ℝ)
    (f : E n → ℝ) (hf : IsHStrongConvex P H f) (x y : E n) (hx : x ∈ P) (hy : y ∈ P) :
    2 * (f x - f y) ≤ 2 * inner ℝ (gradient f x) (x - y) - H * ‖y - x‖ ^ 2 := by sorry

end LogRegretOCO.OGD

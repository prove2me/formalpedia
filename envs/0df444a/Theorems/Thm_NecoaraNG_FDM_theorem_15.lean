-- Prove2me | Theorems.Thm_NecoaraNG_FDM_theorem_15
-- name    : NecoaraNG.FDM.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:27.175796+00:00
-- url     : https://prove2.me/theorems/33a6a9b5-6fcb-4d21-8232-a24ee6ee6f2c
-- title:
--   Theorem 15, p. 29 — (FDM) converges linearly in function values on F_{L_f,κ_f} with rate 1/(1 + Lκ_f/(4(L_f + L̄_f + βL̄_f)²))
-- statement:
--   Consider problem $(\mathrm P)$: $f^*=\min_{x\in X}f(x)$, where $X\subseteq\mathbb R^n$ is closed and convex, $f:\mathbb R^n\to\mathbb R$ is convex on $X$ and differentiable at every point of $X$ with gradient Lipschitz on $X$ with constant $L_f>0$,
--   $$
--   \|\nabla f(x)-\nabla f(y)\|\le L_f\|x-y\|\qquad\text{for all } x,y\in X ,
--   $$
--   and the optimal set $X^*$ is nonempty, with $x^*\in X^*$ and $f^*=f(x^*)$. Assume $f$ has **quadratic functional growth** with constant $\kappa_f>0$: for every $x\in X$ and every nearest point $\bar x=[x]_{X^*}$, $f(x)-f^*\ge\frac{\kappa_f}2\|x-\bar x\|^2$. Together these say $f$ belongs to the class $\mathcal F_{L_f,\kappa_f}(X)$.
--
--   Let $\beta,L,\bar L_f>0$ and let $(x^k)$, $(e^k)$, $(\alpha_k)$ be a run of the **feasible descent method (FDM)**: $x^0\in X$ and, for every $k\ge0$,
--   $$
--   x^{k+1}=\big[x^k-\alpha_k\nabla f(x^k)+e^k\big]_X,\quad \|e^k\|\le\beta\|x^{k+1}-x^k\|,\quad f(x^{k+1})\le f(x^k)-\frac L2\|x^{k+1}-x^k\|^2,\quad \alpha_k\ge\bar L_f^{-1}.
--   $$
--   Then for every $k\ge0$
--   $$
--   f(x^k)-f^*\ \le\ \left(\frac{1}{1+\dfrac{L\kappa_f}{4(L_f+\bar L_f+\beta\bar L_f)^2}}\right)^{k}\big(f(x^0)-f^*\big). \tag{64}
--   $$
--
--   The theorem shows that the whole family of feasible descent methods, which includes proximal point, coordinate descent, extragradient and matrix splitting methods, converges linearly in function values under quadratic functional growth, without strong convexity and without assuming an error bound.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; $f$ is defined on all of $\mathbb R^n$ and only its values and gradients at points of $X$ matter. The projection is the predicate `IsNearest`, so a run is any pair of sequences satisfying the conditions, and the errors $e^k$ are quantified together with the iterates. "Simple" (cheap projection) and "closed" for $f$ are dropped: the first is not a mathematical condition and the second follows from continuity on $X$. No upper bound on $\alpha_k$ is assumed, as on the page.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 29, Theorem 15, (64)

import Mathlib
import Definitions.Def_NecoaraNG_FDM_Setting

namespace NecoaraNG.FDM

open scoped InnerProductSpace

/-- Theorem 15, p. 29, (64): for `f` in the class `F_{L_f, κ}(X)` (convex, (1), (22)), every run of
the feasible descent method (FDM) satisfies
`f(x^k) - f* ≤ (1 / (1 + L κ / (4 (L_f + L̄_f + β L̄_f)²)))^k (f(x⁰) - f*)`, with `f* = f x*`. -/
theorem theorem_15 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hF : NecoaraNG.Chain.QuadFunGrowth X f κ)
    (β L Lbar : ℝ) (hβ : 0 < β) (hLpos : 0 < L) (hLbar : 0 < Lbar)
    (α : ℕ → ℝ) (e x : ℕ → NecoaraNG.Chain.E n) (hrun : IsFDMRun X f β L Lbar α e x) :
    ∀ k : ℕ, f (x k) - f xstar ≤
      (1 / (1 + L * κ / (4 * (Lf + Lbar + β * Lbar) ^ 2))) ^ k * (f (x 0) - f xstar) := by sorry

end NecoaraNG.FDM

-- Prove2me | Theorems.Thm_KarimiPL_GD_theorem_1
-- name    : KarimiPL.GD.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:59.927491+00:00
-- url     : https://prove2.me/theorems/943f38b3-7585-4cf3-ab6a-753fdd8abe3e
-- title:
--   Theorem 1 — gradient descent under PL converges at rate (1 − μ/L)^k
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be differentiable with an $L$-Lipschitz gradient, where $L>0$. Suppose $x^*$ is a global minimizer and $\mu>0$ satisfies the Polyak–Łojasiewicz inequality $\frac12\|\nabla f(z)\|^2\ge\mu(f(z)-f(x^*))$ for every $z$. Starting from any $x_0$, define $x_{k+1}=x_k-L^{-1}\nabla f(x_k)$. Then, for every $k\ge0$,
--
--   $$
--   f(x_k)-f(x^*)\le\left(1-\frac\mu L\right)^k\bigl(f(x_0)-f(x^*)\bigr).
--   $$
--
--   This is the global function-value rate of Theorem 1. It applies without convexity and fixes the reference value to an attained global minimum.
--
--   **Formalization Note** The Lean statement permits $d=0$ and does not add $\mu\le L$. Its `gradient` denotes the derivative because differentiability is explicit. The minimizer hypothesis prevents the PL reference value from being chosen freely.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Theorem 1, equations (1)–(4), p. 2

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
open scoped InnerProductSpace

namespace KarimiPL.GD

theorem theorem_1 {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ y, f xstar ≤ f y)
    (mu : ℝ) (hmu : 0 < mu)
    (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) mu (f xstar))
    (x : ℕ → EuclideanSpace ℝ (Fin d))
    (hx : ∀ k, x (k + 1) = x k - (1 / L) • gradient f (x k)) :
    ∀ k : ℕ, f (x k) - f xstar ≤ (1 - mu / L) ^ k * (f (x 0) - f xstar) := by sorry

end KarimiPL.GD

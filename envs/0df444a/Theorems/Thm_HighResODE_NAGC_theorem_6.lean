-- Prove2me | Theorems.Thm_HighResODE_NAGC_theorem_6
-- name    : HighResODE.NAGC.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:17.932301+00:00
-- url     : https://prove2.me/theorems/66767747-7d55-4aed-8ec5-2d6d277ddfa1
-- title:
--   Theorem 6, p. 24 — NAG-C: min_{0≤i≤k}‖∇f(xᵢ)‖² ≤ 8568‖x₀ − x⋆‖²/(s²(k + 1)³) and f(xₖ) − f(x⋆) ≤ 119‖x₀ − x⋆‖²/(s(k + 1)²)
-- statement:
--   Let $f\in\mathcal F^1_L(\mathbb R^n)$ be convex with $L$-Lipschitz gradient, $L>0$, and let $x^\star$ be a minimizer of $f$. Let $0<s\le 1/(3L)$ and let $(x_k)_{k\ge0}$ be the iterates of NAG-C,
--   $$
--   y_{k+1}=x_k-s\nabla f(x_k),\qquad x_{k+1}=y_{k+1}+\frac{k}{k+3}(y_{k+1}-y_k),\qquad y_0=x_0 .
--   $$
--   Then for every $k\ge0$
--   $$
--   \min_{0\le i\le k}\|\nabla f(x_i)\|^2\le\frac{8568\,\|x_0-x^\star\|^2}{s^2(k+1)^3}
--   \qquad\text{and}\qquad
--   f(x_k)-f(x^\star)\le\frac{119\,\|x_0-x^\star\|^2}{s(k+1)^2}.
--   $$
--
--   With $s=1/(3L)$ the first bound is $O(L^2\|x_0-x^\star\|^2/k^3)$: NAG-C, without modification, minimizes the squared gradient norm at an inverse cubic rate, faster than the $O(L^2/k^2)$ that follows from the function-value rate and $L$-smoothness.
--
--   **Formalization Note** Both claims of the theorem are one conjunction. The minimum over $0\le i\le k$ is `Finset.inf'` over `Finset.range (k + 1)`. The minimizer $x^\star$ is a hypothesis: the paper presupposes its existence for a merely convex $f$. The algorithm is a predicate on the two sequences, which determines them from $x_0$; the momentum $k/(k+3)$ is a real quotient.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 24, Theorem 6

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- Theorem 6, p. 24. -/
theorem theorem_6 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : HighResODE.NAGSC.IsF1 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L))
    (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) :
    (∀ k : ℕ, (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
        (fun i => ‖gradient f (x i)‖ ^ 2)
          ≤ 8568 * ‖x 0 - xs‖ ^ 2 / (s ^ 2 * ((k : ℝ) + 1) ^ 3)) ∧
    (∀ k : ℕ, f (x k) - f xs ≤ 119 * ‖x 0 - xs‖ ^ 2 / (s * ((k : ℝ) + 1) ^ 2)) := by sorry

end HighResODE.NAGC

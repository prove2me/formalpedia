-- Prove2me | Theorems.Thm_HighResODE_NAGC_C_1_2
-- name    : HighResODE.NAGC.C_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:54.15399+00:00
-- url     : https://prove2.me/theorems/b2905244-98fb-43f0-9206-9ab252f04c4f
-- title:
--   App. C.1.2, p. 60 — ‖∇f(xₖ)‖² at k = 0, 1, 2, 3 is at most 1/9, 20/81, 485/972, 2372/2187 times ‖x₀ − x⋆‖²/s²
-- statement:
--   Let $f\in\mathcal F^1_L(\mathbb R^n)$, let $x^\star$ be a minimizer of $f$, let $0<s\le 1/(3L)$, and let $(x_k,y_k)$ be a run of NAG-C with step size $s$. Then
--   $$
--   \|\nabla f(x_0)\|^2\le\frac{\|x_0-x^\star\|^2}{9s^2},\quad
--   \|\nabla f(x_1)\|^2\le\frac{20\|x_0-x^\star\|^2}{81s^2},\quad
--   \|\nabla f(x_2)\|^2\le\frac{485\|x_0-x^\star\|^2}{972s^2},\quad
--   \|\nabla f(x_3)\|^2\le\frac{2372\|x_0-x^\star\|^2}{2187s^2}.
--   $$
--
--   These cover the first four iterates, which the Lyapunov argument for $k\ge4$ does not reach; together with (4.11) they give the gradient claim of Theorem 6 for every $k\ge0$.
--
--   **Formalization Note** The minimizer $x^\star$ is a hypothesis.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 60, App. C.1.2 (consequence of (C.4)–(C.6))

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- App. C.1.2, p. 60: the squared gradient norms at `k = 0, 1, 2, 3`. -/
theorem C_1_2 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : HighResODE.NAGSC.IsF1 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L))
    (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) :
    ‖gradient f (x 0)‖ ^ 2 ≤ ‖x 0 - xs‖ ^ 2 / (9 * s ^ 2) ∧
    ‖gradient f (x 1)‖ ^ 2 ≤ 20 * ‖x 0 - xs‖ ^ 2 / (81 * s ^ 2) ∧
    ‖gradient f (x 2)‖ ^ 2 ≤ 485 * ‖x 0 - xs‖ ^ 2 / (972 * s ^ 2) ∧
    ‖gradient f (x 3)‖ ^ 2 ≤ 2372 * ‖x 0 - xs‖ ^ 2 / (2187 * s ^ 2) := by sorry

end HighResODE.NAGC

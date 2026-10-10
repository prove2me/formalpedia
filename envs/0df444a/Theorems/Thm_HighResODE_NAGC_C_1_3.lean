-- Prove2me | Theorems.Thm_HighResODE_NAGC_C_1_3
-- name    : HighResODE.NAGC.C_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:52.126187+00:00
-- url     : https://prove2.me/theorems/8cd13123-cef3-45d5-a8ca-2c8b2d71b4b3
-- title:
--   App. C.1.3, p. 61 — f(x₀) − f(x⋆) ≤ ‖x₀ − x⋆‖²/(6s) and f(x₁) − f(x⋆) ≤ 10‖x₀ − x⋆‖²/(27s)
-- statement:
--   Let $f\in\mathcal F^1_L(\mathbb R^n)$, let $x^\star$ be a minimizer of $f$, let $0<s\le 1/(3L)$, and let $(x_k,y_k)$ be a run of NAG-C with step size $s$. Then
--   $$
--   f(x_0)-f(x^\star)\le\frac{\|x_0-x^\star\|^2}{6s},\qquad f(x_1)-f(x^\star)\le\frac{10\|x_0-x^\star\|^2}{27s}.
--   $$
--
--   These cover the two iterates that the function-value part of the Lyapunov argument, valid for $k\ge2$, does not reach.
--
--   **Formalization Note** The minimizer $x^\star$ is a hypothesis.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 61, App. C.1.3 (consequence of (C.7))

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- App. C.1.3, p. 61: the objective gaps at `k = 0, 1`. -/
theorem C_1_3 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : HighResODE.NAGSC.IsF1 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L))
    (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) :
    f (x 0) - f xs ≤ ‖x 0 - xs‖ ^ 2 / (6 * s) ∧
    f (x 1) - f xs ≤ 10 * ‖x 0 - xs‖ ^ 2 / (27 * s) := by sorry

end HighResODE.NAGC

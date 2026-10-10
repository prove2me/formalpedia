-- Prove2me | Theorems.Thm_HighResODE_NAGCODE_eq_4_4
-- name    : HighResODE.NAGCODE.eq_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:44.679895+00:00
-- url     : https://prove2.me/theorems/6dd8b7f1-49de-4706-811a-3f2f185b57e7
-- title:
--   (4.4), p. 22 — inf_{t₀≤u≤t}‖∇f(X(u))‖² ≤ (2 + 1.5sL)‖x₀ − x⋆‖²/(√s(t³ − t₀³)/3 + (1/L + s/2)(t² − t₀²)/2 + (√s/(2L))(t − t₀))
-- statement:
--   Let $f\in\mathcal F^2_L(\mathbb R^n)$, let $x^\star$ be a minimizer of $f$, let $s>0$ and $t_0=1.5\sqrt s$, and let $X$ solve the high-resolution ODE of NAG-C (1.12) from $x_0$. Then for every $t>t_0$,
--   $$\inf_{t_0\le u\le t}\|\nabla f(X(u))\|^2\le\frac{(2+1.5sL)\|x_0-x^\star\|^2}{\sqrt s(t^3-t_0^3)/3+(\frac1L+\frac s2)(t^2-t_0^2)/2+\frac{\sqrt s}{2L}(t-t_0)} .$$
--
--   Keeping only the first term of the denominator gives Theorem 5.
--
--   **Formalization Note** The infimum is over the points of $[t_0,t]$, as in (4.3).
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 22, (4.4)

import Mathlib
import Definitions.Def_HighResODE_NAGCODE_Setting

namespace HighResODE.NAGCODE

open scoped InnerProductSpace

/-- (4.4), p. 22: for `t > t₀`,
`inf_{t₀≤u≤t} ‖∇f(X(u))‖² ≤ (2 + 1.5sL)‖x₀ − x⋆‖²/(√s(t³ − t₀³)/3 + (1/L + s/2)(t² − t₀²)/2 + (√s/(2L))(t − t₀))`. -/
theorem eq_4_4 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : IsF2 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsNAGCODE f s x0 X V) :
    ∀ t : ℝ, t0 s < t →
      (⨅ u : Set.Icc (t0 s) t, ‖gradient f (X u)‖ ^ 2)
        ≤ (2 + 1.5 * s * L) * ‖x0 - xs‖ ^ 2 /
          (Real.sqrt s * (t ^ 3 - (t0 s) ^ 3) / 3 + (1 / L + s / 2) * (t ^ 2 - (t0 s) ^ 2) / 2
        + Real.sqrt s / (2 * L) * (t - t0 s)) := by sorry

end HighResODE.NAGCODE

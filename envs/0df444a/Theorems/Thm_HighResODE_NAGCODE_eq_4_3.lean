-- Prove2me | Theorems.Thm_HighResODE_NAGCODE_eq_4_3
-- name    : HighResODE.NAGCODE.eq_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:53.333252+00:00
-- url     : https://prove2.me/theorems/f601314c-c96d-434f-8aa3-7671c6a2ea85
-- title:
--   (4.3), p. 22 — inf_{t₀≤u≤t}‖∇f(X(u))‖² ≤ E(t₀)/(√s(t³ − t₀³)/3 + (1/L + s/2)(t² − t₀²)/2 + (√s/(2L))(t − t₀))
-- statement:
--   Let $f\in\mathcal F^2_L(\mathbb R^n)$, let $x^\star$ be a minimizer of $f$, let $s>0$ and $t_0=1.5\sqrt s$, and let $X$ solve the high-resolution ODE of NAG-C (1.12) from $x_0$, with Lyapunov function $\mathcal E$ of (4.1). Write $w(u)=\sqrt s\,u^2+(\frac1L+\frac s2)u+\frac{\sqrt s}{2L}$. Then for every $t>t_0$,
--   $$\inf_{t_0\le u\le t}\|\nabla f(X(u))\|^2\le\frac{\int_{t_0}^t w(u)\|\nabla f(X(u))\|^2\,du}{\int_{t_0}^t w(u)\,du}\le\frac{\mathcal E(t_0)}{\sqrt s(t^3-t_0^3)/3+(\frac1L+\frac s2)(t^2-t_0^2)/2+\frac{\sqrt s}{2L}(t-t_0)} .$$
--
--   This converts the integral bound into a bound on the smallest squared gradient norm along the trajectory up to time $t$.
--
--   **Formalization Note** The infimum is taken over the points $u$ of the interval $[t_0,t]$ (a nonempty set on which the squared norm is bounded below by $0$), so it is the genuine infimum.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 22, (4.3)

import Mathlib
import Definitions.Def_HighResODE_NAGCODE_Setting

namespace HighResODE.NAGCODE

open scoped InnerProductSpace

/-- (4.3), p. 22: for `t > t₀`, `inf_{t₀≤u≤t} ‖∇f(X(u))‖²` is at most the ratio of the weighted integral
to the integral of the weight, which is at most
`E(t₀)/(√s(t³ − t₀³)/3 + (1/L + s/2)(t² − t₀²)/2 + (√s/(2L))(t − t₀))`. -/
theorem eq_4_3 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : IsF2 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsNAGCODE f s x0 X V) :
    ∀ t : ℝ, t0 s < t →
      (⨅ u : Set.Icc (t0 s) t, ‖gradient f (X u)‖ ^ 2)
          ≤ (∫ u in (t0 s)..t, (Real.sqrt s * u ^ 2 + (1 / L + s / 2) * u + Real.sqrt s / (2 * L)) * ‖gradient f (X u)‖ ^ 2)
            / (∫ u in (t0 s)..t, (Real.sqrt s * u ^ 2 + (1 / L + s / 2) * u + Real.sqrt s / (2 * L))) ∧
      (∫ u in (t0 s)..t, (Real.sqrt s * u ^ 2 + (1 / L + s / 2) * u + Real.sqrt s / (2 * L)) * ‖gradient f (X u)‖ ^ 2)
            / (∫ u in (t0 s)..t, (Real.sqrt s * u ^ 2 + (1 / L + s / 2) * u + Real.sqrt s / (2 * L)))
          ≤ lyap f s xs X V (t0 s) /
            (Real.sqrt s * (t ^ 3 - (t0 s) ^ 3) / 3 + (1 / L + s / 2) * (t ^ 2 - (t0 s) ^ 2) / 2
        + Real.sqrt s / (2 * L) * (t - t0 s)) := by sorry

end HighResODE.NAGCODE

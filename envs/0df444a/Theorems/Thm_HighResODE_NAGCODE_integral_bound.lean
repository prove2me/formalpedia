-- Prove2me | Theorems.Thm_HighResODE_NAGCODE_integral_bound
-- name    : HighResODE.NAGCODE.integral_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:50.203985+00:00
-- url     : https://prove2.me/theorems/12211fce-db56-4ba6-954a-9e970748dce5
-- title:
--   p. 22, display after Lemma 4.1 — ∫_{t₀}^t [√s u² + (1/L + s/2)u + √s/(2L)]‖∇f(X(u))‖² du ≤ E(t₀) − E(t) ≤ E(t₀)
-- statement:
--   Let $f\in\mathcal F^2_L(\mathbb R^n)$, let $x^\star$ be a minimizer of $f$, let $s>0$ and $t_0=1.5\sqrt s$, and let $X$ solve the high-resolution ODE of NAG-C (1.12) from $x_0$, with Lyapunov function $\mathcal E$ of (4.1). For every $t\ge t_0$, the function $u\mapsto\big[\sqrt s\,u^2+(\frac1L+\frac s2)u+\frac{\sqrt s}{2L}\big]\|\nabla f(X(u))\|^2$ is integrable on $[t_0,t]$ and
--   $$\int_{t_0}^{t}\Big[\sqrt s\,u^2+\Big(\frac1L+\frac s2\Big)u+\frac{\sqrt s}{2L}\Big]\|\nabla f(X(u))\|^2\,du\le\mathcal E(t_0)-\mathcal E(t)\le\mathcal E(t_0).$$
--
--   The first inequality integrates Lemma 4.1; the second is $\mathcal E(t)\ge0$, which holds because $x^\star$ is a minimizer.
--
--   **Formalization Note** Integrability on $[t_0,t]$ is part of the conclusion, so the bound cannot hold merely because a non-integrable integrand has Lean integral $0$.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 22, display after Lemma 4.1

import Mathlib
import Definitions.Def_HighResODE_NAGCODE_Setting

namespace HighResODE.NAGCODE

open scoped InnerProductSpace

/-- Display after Lemma 4.1, p. 22: for `t ≥ t₀` the weight `[√s u² + (1/L + s/2)u + √s/(2L)]‖∇f(X(u))‖²`
is integrable on `[t₀, t]`, its integral is at most `ℰ(t₀) − ℰ(t)`, and `ℰ(t₀) − ℰ(t) ≤ ℰ(t₀)`. -/
theorem integral_bound {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : IsF2 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsNAGCODE f s x0 X V) :
    ∀ t : ℝ, t0 s ≤ t →
      IntervalIntegrable (fun u => (Real.sqrt s * u ^ 2 + (1 / L + s / 2) * u + Real.sqrt s / (2 * L)) * ‖gradient f (X u)‖ ^ 2)
        MeasureTheory.volume (t0 s) t ∧
      (∫ u in (t0 s)..t, (Real.sqrt s * u ^ 2 + (1 / L + s / 2) * u + Real.sqrt s / (2 * L)) * ‖gradient f (X u)‖ ^ 2)
        ≤ lyap f s xs X V (t0 s) - lyap f s xs X V t ∧
      lyap f s xs X V (t0 s) - lyap f s xs X V t ≤ lyap f s xs X V (t0 s) := by sorry

end HighResODE.NAGCODE

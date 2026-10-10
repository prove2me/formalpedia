-- Prove2me | Theorems.Thm_HighResODE_NAGCODE_lemma_4_1
-- name    : HighResODE.NAGCODE.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:05.332114+00:00
-- url     : https://prove2.me/theorems/5c7347a1-8fbe-4e53-9ba4-e2332f5ab320
-- title:
--   Lemma 4.1 (4.2), p. 22 — along (1.12), dE/dt ≤ −[√s t² + (1/L + s/2)t + √s/(2L)]‖∇f(X)‖² for t ≥ t₀
-- statement:
--   Let $f\in\mathcal F^2_L(\mathbb R^n)$, let $x^\star$ be a minimizer of $f$, let $s>0$ be an arbitrary step size and $t_0=1.5\sqrt s$, and let $X$ solve the high-resolution ODE of NAG-C (1.12) from $x_0$. Then for every $t\ge t_0$ the Lyapunov function $\mathcal E$ of (4.1) has a derivative at $t$ (relative to $[t_0,\infty)$), and
--   $$\frac{d\mathcal E(t)}{dt}\le-\Big[\sqrt s\,t^2+\Big(\frac1L+\frac s2\Big)t+\frac{\sqrt s}{2L}\Big]\|\nabla f(X(t))\|^2 .$$
--
--   The gradient-norm factor on the right comes from the gradient-correction term of the ODE. Integrating this bound is the core of Theorem 5.
--
--   **Formalization Note** The derivative is asserted to exist (with the bound) rather than written as `deriv`, which would be $0$ at a point of non-differentiability.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 22, Lemma 4.1, (4.2)

import Mathlib
import Definitions.Def_HighResODE_NAGCODE_Setting

namespace HighResODE.NAGCODE

open scoped InnerProductSpace

/-- Lemma 4.1 (4.2), p. 22: `dE/dt ≤ −[√s t² + (1/L + s/2)t + √s/(2L)]‖∇f(X)‖²` for all `t ≥ t₀`. -/
theorem lemma_4_1 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : IsF2 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsNAGCODE f s x0 X V) :
    ∀ t : ℝ, t0 s ≤ t → ∃ e' : ℝ,
      HasDerivWithinAt (lyap f s xs X V) e' (Set.Ici (t0 s)) t ∧
      e' ≤ -(Real.sqrt s * t ^ 2 + (1 / L + s / 2) * t + Real.sqrt s / (2 * L))
        * ‖gradient f (X t)‖ ^ 2 := by sorry

end HighResODE.NAGCODE

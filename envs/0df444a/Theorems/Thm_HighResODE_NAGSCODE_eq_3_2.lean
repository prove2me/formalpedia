-- Prove2me | Theorems.Thm_HighResODE_NAGSCODE_eq_3_2
-- name    : HighResODE.NAGSCODE.eq_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:20.518773+00:00
-- url     : https://prove2.me/theorems/b3ffaa31-09ca-431c-9c64-1c56c124ebc3
-- title:
--   (3.2), proof of Theorem 1, p. 13 — E(t) ≤ e^{−√μ t/4} E(0) along the NAG-SC high-resolution ODE
-- statement:
--   Let $f\in\mathcal S^2_{\mu,L}(\mathbb R^n)$ with minimizer $x^\star$, let $s>0$, let $X$ solve the high-resolution ODE (1.11) of NAG-SC with $X(0)=x_0$ and $\dot X(0)=-2\sqrt s\,\nabla f(x_0)/(1+\sqrt{\mu s})$, and let $\mathcal E$ be the Lyapunov function (2.4). Then for every $t\ge0$,
--   $$\mathcal E(t)\le e^{-\frac{\sqrt\mu t}{4}}\,\mathcal E(0).\tag{3.2}$$
--
--   This is the integrated form of Lemma 3.1; evaluating $\mathcal E(0)$ at the initial conditions and bounding it by $\|x_0-x^\star\|^2$ yields Theorem 1.
--
--   **Formalization Note.** Every step size $s>0$ is allowed; the restriction $s\le1/L$ of Theorem 1 enters only when $\mathcal E(0)$ is estimated.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 13, proof of Theorem 1, (3.2)

import Mathlib
import Definitions.Def_HighResODE_NAGSCODE_Setting

open scoped InnerProductSpace

namespace HighResODE.NAGSCODE

theorem eq_3_2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L)
    (xs : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xs ≤ f z) (hs : 0 < s)
    (x0 : EuclideanSpace ℝ (Fin n)) (X V : ℝ → EuclideanSpace ℝ (Fin n))
    (hsol : IsNAGSCODE f μ s x0 X V) :
    ∀ t, 0 ≤ t →
      lyap f μ s xs X V t ≤ Real.exp (-(Real.sqrt μ * t / 4)) * lyap f μ s xs X V 0 := by sorry

end HighResODE.NAGSCODE

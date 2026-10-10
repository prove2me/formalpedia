-- Prove2me | Theorems.Thm_HighResODE_HeavyBallODE_lyap_le_exp
-- name    : HighResODE.HeavyBallODE.lyap_le_exp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:27.868161+00:00
-- url     : https://prove2.me/theorems/9d4444f5-0fdf-4efa-972f-82eb31430519
-- title:
--   Proof of Theorem 2, p. 14 — E(t) ≤ e^{−√μ t/4} E(0) along the high-resolution heavy-ball ODE
-- statement:
--   Let $f\in\mathcal S^2_{\mu,L}(\mathbb R^n)$ with minimizer $x^\star$, let $s>0$, and let $(X,\dot X)$ be the solution of the high-resolution heavy-ball ODE (1.10) started at $x_0$. Then the Lyapunov function (3.3) satisfies, for every $t\ge0$,
--   $$\mathcal E(t)\le e^{-\sqrt\mu\,t/4}\,\mathcal E(0).$$
--
--   This is the integrated form of Lemma 3.2, obtained in the paper "by integrating over the time parameter $t$"; combined with an estimate of $\mathcal E(0)$ it gives Theorem 2.
--
--   **Formalization Note.** As in Lemma 3.2, the solution is any pair $(X,V)$ satisfying (1.10) on $[0,\infty)$ with its initial conditions, and $x^\star$ is a point with $f(x^\star)\le f(z)$ for all $z$.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 14, proof sketch of Theorem 2

import Mathlib
import Definitions.Def_HighResODE_HeavyBallODE_Setting

namespace HighResODE.HeavyBallODE

theorem lyap_le_exp {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsHeavyBallODE f μ s x0 X V) :
    ∀ t : ℝ, 0 ≤ t →
      lyap f μ s xs X V t ≤ Real.exp (-(Real.sqrt μ * t / 4)) * lyap f μ s xs X V 0 := by sorry

end HighResODE.HeavyBallODE

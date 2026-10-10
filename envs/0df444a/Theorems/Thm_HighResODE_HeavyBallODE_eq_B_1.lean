-- Prove2me | Theorems.Thm_HighResODE_HeavyBallODE_eq_B_1
-- name    : HighResODE.HeavyBallODE.eq_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:25:57.988965+00:00
-- url     : https://prove2.me/theorems/0dcec334-51eb-48e6-b41b-cc9712062f45
-- title:
--   (B.1), p. 50 — E ≤ (1 + √(μs))(f(X) − f(x⋆)) + (3/4)‖Ẋ‖² + 2μ‖X − x⋆‖²
-- statement:
--   Let $\mu\ge 0$ and $s$ be real numbers, let $f:\mathbb R^n\to\mathbb R$, let $x^\star\in\mathbb R^n$, and let $X,V$ be curves in $\mathbb R^n$ (with $V$ playing the role of $\dot X$). Let $\mathcal E$ be the Lyapunov function (3.3),
--   $$\mathcal E(t)=\bigl(1+\sqrt{\mu s}\bigr)\bigl(f(X(t))-f(x^\star)\bigr)+\frac14\|V(t)\|^2+\frac14\bigl\|V(t)+2\sqrt{\mu}\,(X(t)-x^\star)\bigr\|^2 .$$
--   Then for every $t$,
--   $$\mathcal E(t)\le \bigl(1+\sqrt{\mu s}\bigr)\bigl(f(X(t))-f(x^\star)\bigr)+\frac34\|V(t)\|^2+2\mu\|X(t)-x^\star\|^2 .$$
--
--   This is the upper estimate (B.1) of the Lyapunov function, obtained from $\|a+b\|^2\le2(\|a\|^2+\|b\|^2)$. It is used in the proof of Lemma 3.2 and to bound $\mathcal E(0)$ in the proof of Theorem 2.
--
--   **Formalization Note.** The estimate is an inequality between values and holds for arbitrary curves, so the ODE, the function class and the minimality of $x^\star$ are not assumed; only $\mu\ge0$ is needed (so that $(\sqrt\mu)^2=\mu$).
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 50, App. B.1, (B.1)

import Mathlib
import Definitions.Def_HighResODE_HeavyBallODE_Setting

namespace HighResODE.HeavyBallODE

open scoped InnerProductSpace

theorem eq_B_1 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ s : ℝ) (hμ : 0 ≤ μ) (xs : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (t : ℝ) :
    lyap f μ s xs X V t ≤ (1 + Real.sqrt (μ * s)) * (f (X t) - f xs) + 3 / 4 * ‖V t‖ ^ 2
      + 2 * μ * ‖X t - xs‖ ^ 2 := by sorry

end HighResODE.HeavyBallODE

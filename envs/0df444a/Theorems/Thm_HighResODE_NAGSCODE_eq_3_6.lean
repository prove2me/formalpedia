-- Prove2me | Theorems.Thm_HighResODE_NAGSCODE_eq_3_6
-- name    : HighResODE.NAGSCODE.eq_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:13.014332+00:00
-- url     : https://prove2.me/theorems/835e3d1e-7cee-42b7-b193-e6ca4fe10332
-- title:
--   (3.6), p. 15 — E(t) ≤ (1+√(μs))(f(X)−f(x⋆)) + ‖Ẋ‖² + 3μ‖X−x⋆‖² + (3s/4)‖∇f(X)‖²
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, $x^\star\in\mathbb R^n$, $\mu\ge0$ and $s\ge0$, and let $X,\dot X$ be any curves in $\mathbb R^n$. The Lyapunov function (2.4),
--   $$\mathcal E(t)=\big(1+\sqrt{\mu s}\big)\big(f(X)-f(x^\star)\big)+\frac14\|\dot X\|^2+\frac14\big\|\dot X+2\sqrt\mu(X-x^\star)+\sqrt s\nabla f(X)\big\|^2,$$
--   satisfies, at every time $t$ (with $X=X(t)$, $\dot X=\dot X(t)$),
--   $$\mathcal E(t)\le\big(1+\sqrt{\mu s}\big)\big(f(X)-f(x^\star)\big)+\|\dot X\|^2+3\mu\|X-x^\star\|^2+\frac{3s}{4}\|\nabla f(X)\|^2.$$
--
--   It is the upper bound on $\mathcal E$ that, combined with the dissipation bound (3.5), turns the derivative estimate into the rate $-\frac{\sqrt\mu}{4}\mathcal E$ of Lemma 3.1.
--
--   **Formalization Note.** The inequality is pointwise in $t$ and uses only $\|a+b+c\|^2\le3(\|a\|^2+\|b\|^2+\|c\|^2)$; it is therefore stated for arbitrary $f$, arbitrary curves and $\mu,s\ge0$, which contains the page's setting (where $f\in\mathcal S^2_{\mu,L}$ and $X$ solves (1.11)) as a special case. $\dot X$ is the velocity curve $V$.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 15, proof of Lemma 3.1, (3.6)

import Mathlib
import Definitions.Def_HighResODE_NAGSCODE_Setting

open scoped InnerProductSpace

namespace HighResODE.NAGSCODE

theorem eq_3_6 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ s : ℝ) (hμ : 0 ≤ μ) (hs : 0 ≤ s)
    (xs : EuclideanSpace ℝ (Fin n)) (X V : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    lyap f μ s xs X V t ≤ (1 + Real.sqrt (μ * s)) * (f (X t) - f xs) + ‖V t‖ ^ 2
      + 3 * μ * ‖X t - xs‖ ^ 2 + 3 * s / 4 * ‖gradient f (X t)‖ ^ 2 := by sorry

end HighResODE.NAGSCODE

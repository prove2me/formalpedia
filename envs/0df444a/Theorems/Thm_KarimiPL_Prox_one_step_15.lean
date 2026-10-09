-- Prove2me | Theorems.Thm_KarimiPL_Prox_one_step_15
-- name    : KarimiPL.Prox.one_step_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:46.959984+00:00
-- url     : https://prove2.me/theorems/f7e4cf9e-f5a9-45b2-b71d-5e42466d4a09
-- title:
--   (15), p. 9 — one proximal-gradient step gives $F(x_{k+1}) - F^* \le (1 - \mu/L)[F(x_k) - F^*]$
-- statement:
--   Let $f : \mathbb R^d \to \mathbb R$ be differentiable with an $L$-Lipschitz continuous gradient, $L > 0$, let $g : \mathbb R^d \to \mathbb R$ be convex, and write $F = f + g$. Suppose $F$ has a minimizer $x^*$, write $F^* = F(x^*)$, and suppose $F$ satisfies the proximal-PL inequality (12) with $\mu > 0$:
--   $$
--   \tfrac12\,\mathcal D_g(x, L) \ge \mu\,\bigl(F(x) - F^*\bigr) \qquad \text{for all } x.
--   $$
--   Let $x \in \mathbb R^d$ and let $x^+$ minimize $y \mapsto \langle \nabla f(x), y - x\rangle + \frac L2\|y - x\|^2 + g(y) - g(x)$. Then
--   $$
--   F(x^+) - F^* \le \Bigl(1 - \frac{\mu}{L}\Bigr)\bigl[F(x) - F^*\bigr]. \tag{15}
--   $$
--
--   This is the one-step contraction of the proof of Theorem 5; applying it along the iterates gives the theorem.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, proof of Theorem 5, (15), p. 9

import Mathlib
import Definitions.Def_KarimiPL_Prox_Setting

open InnerProductSpace

namespace KarimiPL.Prox

theorem one_step_15 {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hg : ConvexOn ℝ Set.univ g)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ y, f xstar + g xstar ≤ f y + g y)
    (μ : ℝ) (hμ : 0 < μ) (hPPL : ProxPL f g L μ (f xstar + g xstar)) :
    ∀ x y : EuclideanSpace ℝ (Fin d), (∀ z, proxModel f g x L y ≤ proxModel f g x L z) →
      (f y + g y) - (f xstar + g xstar) ≤ (1 - μ / L) * ((f x + g x) - (f xstar + g xstar)) := by sorry

end KarimiPL.Prox

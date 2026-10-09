-- Prove2me | Theorems.Thm_KarimiPL_Prox_descent_Dg
-- name    : KarimiPL.Prox.descent_Dg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:54.141691+00:00
-- url     : https://prove2.me/theorems/aaa44204-f596-4d95-a6a4-0f44b17bb553
-- title:
--   Proof of Theorem 5, p. 9 — a proximal-gradient step gives $F(x_{k+1}) \le F(x_k) - \frac{1}{2L}\mathcal D_g(x_k, L)$
-- statement:
--   Let $f : \mathbb R^d \to \mathbb R$ be differentiable with an $L$-Lipschitz continuous gradient, $L > 0$, let $g : \mathbb R^d \to \mathbb R$ be convex, and write $F = f + g$. Let $x \in \mathbb R^d$ and let $x^+$ be a proximal-gradient step from $x$ with step size $1/L$, i.e. a minimizer over $y \in \mathbb R^d$ of
--   $$
--   \langle \nabla f(x), y - x\rangle + \frac L2\|y - x\|^2 + g(y) - g(x).
--   $$
--   Then
--   $$
--   F(x^+) \le F(x) - \frac{1}{2L}\,\mathcal D_g(x, L).
--   $$
--
--   This is the first part of the chain of inequalities in the proof of Theorem 5: the decrease of one proximal-gradient step is measured by $\mathcal D_g$, as the decrease of a gradient step is measured by $\|\nabla f\|^2$ in the smooth case.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, proof of Theorem 5, first three lines of the display, p. 9

import Mathlib
import Definitions.Def_KarimiPL_Prox_Setting

open InnerProductSpace

namespace KarimiPL.Prox

theorem descent_Dg {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hg : ConvexOn ℝ Set.univ g) :
    ∀ x y : EuclideanSpace ℝ (Fin d), (∀ z, proxModel f g x L y ≤ proxModel f g x L z) →
      f y + g y ≤ f x + g x - 1 / (2 * L) * Dg f g x L := by sorry

end KarimiPL.Prox

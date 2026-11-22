-- Prove2me | Theorems.Thm_KarimiPL_ProxCD_expected_improvement_eq
-- name    : KarimiPL.ProxCD.expected_improvement_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:29.610136+00:00
-- url     : https://prove2.me/theorems/3ebb3c63-bc09-40a7-b2ba-b6ec8d00e6e4
-- title:
--   Appendix H, p. 23 — (1/d) Σ_i min_t [t∇_i f(x) + (L/2)t² + g_i(x_i + t) − g_i(x_i)] = −(1/(2Ld)) D_g(x, L)
-- statement:
--   Let $d\ge1$, $f:\mathbb R^d\to\mathbb R$, $L>0$, and let $g(x)=\sum_i g_i(x_i)$ with each $g_i:\mathbb R\to\mathbb R$ convex. Then for every $x$,
--   $$\frac1d\sum_{i=1}^d\ \min_{t_i\in\mathbb R}\Big[t_i\nabla_i f(x)+\frac L2 t_i^2+g_i(x_i+t_i)-g_i(x_i)\Big]\ =\ -\frac{1}{2Ld}\,\mathcal D_g(x,L),$$
--   where $\mathcal D_g(x,L)=-2L\min_y\big[\langle\nabla f(x),y-x\rangle+\frac L2\|y-x\|^2+g(y)-g(x)\big]$.
--
--   The left side is the expected best one-coordinate improvement of the upper model when the coordinate is drawn uniformly. Separability of $g$ lets the sum of the coordinate minima be exchanged with the minimum over the full vector $y=x+(t_1,\dots,t_d)$.
--
--   **Formalization Note** Minima are real infima; both are attained because the $g_i$ are convex and $L>0$. The page writes $n$ for the dimension and $\mathcal D_g(L,x)$ for $\mathcal D_g(x,L)$.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Appendix H, display between (62) and (63), p. 23

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_Setting

open InnerProductSpace

namespace KarimiPL.ProxCD

theorem expected_improvement_eq {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ) (L : ℝ) (hL : 0 < L)
    (gs : Fin d → ℝ → ℝ) (hgs : ∀ i, ConvexOn ℝ Set.univ (gs i)) :
    ∀ x : KarimiPL.Rel.E d, (1 / (d : ℝ)) * ∑ i, (⨅ t : ℝ, coordModel f gs L x i t)
      = -(1 / (2 * L * d)) * Dg f (sepSum gs) x L := by sorry

end KarimiPL.ProxCD

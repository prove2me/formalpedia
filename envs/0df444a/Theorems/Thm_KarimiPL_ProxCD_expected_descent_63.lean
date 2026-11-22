-- Prove2me | Theorems.Thm_KarimiPL_ProxCD_expected_descent_63
-- name    : KarimiPL.ProxCD.expected_descent_63
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:21.204176+00:00
-- url     : https://prove2.me/theorems/c82c3da0-393b-4a8e-aa8a-cf2e5903a897
-- title:
--   (63), Appendix H, p. 23 — E[F(x_{k+1})] ≤ F(x_k) − (1/(2Ld)) D_g(x_k, L) under uniform coordinate choice
-- statement:
--   Let $d\ge1$, let $f:\mathbb R^d\to\mathbb R$ be differentiable and satisfy the coordinate-wise $L$-Lipschitz upper bound (5), $L>0$, let $g(x)=\sum_i g_i(x_i)$ with each $g_i:\mathbb R\to\mathbb R$ convex, and $F=f+g$. Let $\mathrm{sel}(x,i)$ be any coordinate proximal-gradient step (16) from $x$ along coordinate $i$, i.e. $\mathrm{sel}(x,i)=x+t^\star e_i$ with $t^\star$ a minimizer of $t\mapsto t\nabla_i f(x)+\frac L2t^2+g_i(x_i+t)-g_i(x_i)$. Then for every $x$,
--   $$\frac1d\sum_{i=1}^d F\big(\mathrm{sel}(x,i)\big)\ \le\ F(x)-\frac{1}{2Ld}\,\mathcal D_g(x,L).$$
--   The left side is $\mathbb E[F(x_{k+1})]$ given $x_k=x$ when $i_k$ is uniform on $\{1,\dots,d\}$.
--
--   This expected-descent inequality, combined with the proximal-PL inequality, gives the contraction factor $1-\mu/(dL)$ of Theorem 6.
--
--   **Formalization Note** The conditional expectation over a uniform coordinate is written as the average over the $d$ coordinates. The page writes $n$ for $d$ and $\mathcal D_g(L,x)$ for $\mathcal D_g(x,L)$.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Appendix H, (63), p. 23

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_Setting

open InnerProductSpace

namespace KarimiPL.ProxCD

theorem expected_descent_63 {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ) (hdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L)
    (hCoord : ∀ (x : KarimiPL.Rel.E d) (i : Fin d) (t : ℝ),
      f (x + t • EuclideanSpace.single i (1 : ℝ)) ≤ f x + t * gradient f x i + L / 2 * t ^ 2)
    (gs : Fin d → ℝ → ℝ) (hgs : ∀ i, ConvexOn ℝ Set.univ (gs i))
    (sel : KarimiPL.Rel.E d → Fin d → KarimiPL.Rel.E d) (hsel : ∀ x i, IsProxCoordStep f gs L x i (sel x i)) :
    ∀ x : KarimiPL.Rel.E d, (1 / (d : ℝ)) * ∑ i, (f (sel x i) + sepSum gs (sel x i))
      ≤ (f x + sepSum gs x) - 1 / (2 * L * d) * Dg f (sepSum gs) x L := by sorry

end KarimiPL.ProxCD

-- Prove2me | Theorems.Thm_KarimiPL_ProxCD_coord_upper_62
-- name    : KarimiPL.ProxCD.coord_upper_62
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:02.442129+00:00
-- url     : https://prove2.me/theorems/db1cb219-656b-4b32-a5e5-6239c5ed298f
-- title:
--   (62), Appendix H, p. 23 — F(x + t e_i) − F(x) ≤ t∇_i f(x) + (L/2)t² + g_i(x_i + t) − g_i(x_i)
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be differentiable and satisfy the coordinate-wise $L$-Lipschitz condition (5), $L>0$: $f(x+t e_i)\le f(x)+t\nabla_i f(x)+(L/2)t^2$ for every $x,i,t$. Let $g(x)=\sum_i g_i(x_i)$ be separable, with arbitrary real-valued $g_i$, and $F=f+g$. Then for every point $x$, coordinate $i$ and step $t\in\mathbb R$,
--   $$F(x+t e_i)-F(x)\ \le\ t\,\nabla_i f(x)+\frac L2\,t^2+g_i(x_i+t)-g_i(x_i).$$
--
--   This is the coordinate-wise upper model that the proximal coordinate step (16) minimizes; it is the first step of the proof of Theorem 6.
--
--   **Formalization Note** The coordinate-wise condition is stated in the exact upper-bound form (5). The full $L$-Lipschitz gradient assumed in Theorem 6 implies it. The page writes $g(x_i)$ for $g_i(x_i)$ in the last term.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Appendix H, (62), p. 23

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_Setting

open InnerProductSpace

namespace KarimiPL.ProxCD

theorem coord_upper_62 {d : ℕ} (f : KarimiPL.Rel.E d → ℝ) (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hCoord : ∀ (x : KarimiPL.Rel.E d) (i : Fin d) (t : ℝ),
      f (x + t • EuclideanSpace.single i (1 : ℝ)) ≤ f x + t * gradient f x i + L / 2 * t ^ 2)
    (gs : Fin d → ℝ → ℝ) :
    ∀ (x : KarimiPL.Rel.E d) (i : Fin d) (t : ℝ),
      (f (x + t • EuclideanSpace.single i (1 : ℝ)) + sepSum gs (x + t • EuclideanSpace.single i (1 : ℝ)))
        - (f x + sepSum gs x) ≤ coordModel f gs L x i t := by sorry

end KarimiPL.ProxCD

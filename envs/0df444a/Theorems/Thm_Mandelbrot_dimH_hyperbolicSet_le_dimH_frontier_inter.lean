-- Prove2me | Theorems.Thm_Mandelbrot_dimH_hyperbolicSet_le_dimH_frontier_inter
-- name    : Mandelbrot.dimH_hyperbolicSet_le_dimH_frontier_inter
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-24T21:43:19.880819+00:00
-- url     : https://prove2.me/theorems/488e9b9c-712e-45fa-a609-62b1427a7d11
-- title:
--   Shishikura: hyperbolic sets transfer to $\partial M$ ($\dim_H(\partial M \cap U) \ge \operatorname{hyp\text{-}dim} J(f_c)$)
-- statement:
--   Let $M$ be the Mandelbrot set and $f_c(z) = z^2 + c$. Let $c_0 \in \partial M$, let $K$ be a hyperbolic set of $f_{c_0}$ (compact, $f_{c_0}(K) \subseteq K$, and $|(f_{c_0}^n)'| > 1$ on $K$ for some $n \geq 1$), and let $U$ be any neighbourhood of $c_0$. Then
--
--   $$\dim_H K \le \dim_H(\partial M \cap U).$$
--
--   In other words, $\dim_H(\partial M \cap U) \geq \operatorname{hyp\text{-}dim} J(f_{c_0})$ for every neighbourhood $U$ of every boundary parameter $c_0$.
--
--   This is the parameter-plane half of Shishikura's argument. A hyperbolic set moves holomorphically, $K_c = h_c(K)$, for $c$ near $c_0$, and its dimension varies continuously. Since $c_0 \in \partial M$, the critical value orbit is not normal near $c_0$, so there are parameters $c_1$ arbitrarily close to $c_0$ where the critical value is mapped onto a point of $K_{c_1}$. Near such a $c_1$, the parameters whose critical value lands in the moving set form a subset of $\partial M$ that is an almost-similar copy of $K_{c_1}$, so its dimension is close to $\dim_H K$.
-- source:
--   M. Shishikura, The Hausdorff dimension of the boundary of the Mandelbrot set and Julia sets, Ann. of Math. (2) 147 (1998), 225-267, https://arxiv.org/abs/math/9201282 (transfer of hyperbolic dimension from the dynamical plane to the parameter plane, used for the Main Theorem)

import Definitions.Def_mandelbrot_hyperbolic_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- **Shishikura (1998), transfer to parameter space**: if `c ∈ ∂M` and `K` is a hyperbolic set
of `z ↦ z ^ 2 + c`, then every neighbourhood `U` of `c` satisfies `dim_H K ≤ dim_H (∂M ∩ U)`.
Equivalently, `dim_H (∂M ∩ U) ≥ hyp-dim J(f_c)`. -/
theorem dimH_hyperbolicSet_le_dimH_frontier_inter (c : ℂ) (hc : c ∈ frontier mandelbrotSet)
    (K : Set ℂ) (hK : IsHyperbolicSet c K) (U : Set ℂ) (hU : U ∈ 𝓝 c) :
    dimH K ≤ dimH (frontier mandelbrotSet ∩ U) := by sorry

end Mandelbrot

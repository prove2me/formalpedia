-- Prove2me | Theorems.Thm_Mandelbrot_exists_hyperbolicSet_dimH_gt
-- name    : Mandelbrot.exists_hyperbolicSet_dimH_gt
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-24T21:43:08.305345+00:00
-- url     : https://prove2.me/theorems/a609f6a8-2133-4d81-93c0-727b2eb8c7df
-- title:
--   Shishikura: boundary parameters with hyperbolic dimension close to $2$
-- statement:
--   Let $M$ be the Mandelbrot set and $f_c(z) = z^2 + c$. For every $d < 2$ there exist a parameter $c \in \partial M$ and a hyperbolic set $K$ of $f_c$ (compact, $f_c(K) \subseteq K$, and $|(f_c^n)'| > 1$ on $K$ for some $n \geq 1$) such that
--
--   $$\dim_H K > d.$$
--
--   Equivalently, $\sup_{c \in \partial M} \operatorname{hyp\text{-}dim} J(f_c) = 2$, where the hyperbolic dimension of $J(f_c)$ is the supremum of $\dim_H K$ over hyperbolic sets $K$ of $f_c$.
--
--   This is the dynamical-plane half of Shishikura's theorem. It comes from parabolic implosion. A map with a parabolic fixed point whose multiplier is a root of unity with $\nu$ petal cycles has hyperbolic dimension greater than $2\nu/(\nu+1)$. Perturbing such a map in parameter space produces maps with more and more petals, whose hyperbolic dimension tends to $2$, and such parameters can be chosen on $\partial M$ (for instance near the cusp $c = 1/4$). Shishikura in fact shows that $\operatorname{hyp\text{-}dim} J(f_c) = 2$ for a residual set of $c \in \partial M$.
-- source:
--   M. Shishikura, The Hausdorff dimension of the boundary of the Mandelbrot set and Julia sets, Ann. of Math. (2) 147 (1998), 225-267, https://arxiv.org/abs/math/9201282 (parabolic implosion estimate for the hyperbolic dimension, used for the Main Theorem)

import Definitions.Def_mandelbrot_hyperbolic_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- **Shishikura (1998), dynamical part**: for every `d < 2` there is a parameter `c` on the
boundary of the Mandelbrot set whose quadratic polynomial `z ↦ z ^ 2 + c` has a hyperbolic set of
Hausdorff dimension greater than `d` (i.e. the hyperbolic dimension of `J(f_c)` exceeds `d`). -/
theorem exists_hyperbolicSet_dimH_gt (d : ENNReal) (hd : d < 2) :
    ∃ c ∈ frontier mandelbrotSet, ∃ K : Set ℂ, IsHyperbolicSet c K ∧ d < dimH K := by sorry

end Mandelbrot

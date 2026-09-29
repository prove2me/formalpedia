-- Prove2me | Theorems.Thm_GrothendieckTeichmuller_sigma3_mem_grt1
-- name    : GrothendieckTeichmuller.sigma3_mem_grt1
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T21:45:57.332315+00:00
-- url     : https://prove2.me/theorems/25456f95-7df7-4a29-a7a4-1717bdee9c63
-- title:
--   The degree-3 element $\sigma_3 = [x+y,[x,y]]$ of $\mathfrak{grt}_1$
-- statement:
--   Write $\mathbb F(x,y)$ for the free Lie algebra over $\mathbb Q$ on two generators and set
--
--   $$\sigma_3 := [\,x+y,\ [x,y]\,] \;=\; [x,[x,y]] - [y,[y,x]] .$$
--
--   Then $\sigma_3$ lies in $\mathfrak{grt}_1$, it is non-zero, and it is homogeneous of degree $3$ (i.e. $\sigma_3(cx,cy) = c^3\sigma_3$ for every rational $c$).
--
--   This is the lowest-degree non-trivial element of the graded Grothendieck-Teichmüller Lie algebra, the degree-$3$ instance of the family $\sigma_3, \sigma_5, \sigma_7,\dots$ produced from the Knizhnik-Zamolodchikov associator. Antisymmetry is immediate, the hexagon equation is the Jacobi identity, and the pentagon equation is a computation in the Drinfeld-Kohno Lie algebra $\mathfrak t_4$.
-- source:
--   Thomas Willwacher, The Grothendieck-Teichmüller Group, ETH Zürich lecture notes (in progress), 27 February 2014, Section 5.1, p. 49, Corollary 5.2 (the element sigma_3 of degree 3 whose non-vanishing is asserted in Corollary 5.2)

import Definitions.Def_GT_grt1

namespace GrothendieckTeichmuller

theorem sigma3_mem_grt1 :
    ⁅gx + gy, ⁅gx, gy⁆⁆ ∈ grt1 ∧ ⁅gx + gy, ⁅gx, gy⁆⁆ ≠ 0 ∧
      IsHomogeneousOfDegree 3 ⁅gx + gy, ⁅gx, gy⁆⁆ := by sorry

end GrothendieckTeichmuller

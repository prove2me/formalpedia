-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_four_spoke_degree20_lower_bounds
-- name    : HermiteLaptop.MaxAgree.four_spoke_degree20_lower_bounds
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-18T15:19:19.259633+00:00
-- url     : https://prove2.me/theorems/3bc4f4d7-48b1-4519-9a43-c89981d8d2a4
-- title:
--   Degree-20 Hermite coefficient lower bounds for four-spoke rounding
-- statement:
--   For four-spoke Gaussian argmax rounding, let $c_{4,m}$ denote the sum over all winning coordinates of the squared Hermite coefficients of total degree $m$. For each $0\le m\le20$, the coefficient satisfies
--   $$c_{4,m}\ge L_m/10^6.$$
--   The integers $L_0,\ldots,L_{20}$, in order of degree, are
--
--   250000, 353204, 101321, 38488, 37526, 17395, 19263, 11063, 11857, 7898, 8181, 5988, 6079, 4729, 4749, 3850, 3845, 3210, 3197, 2728, 2713.
-- source:
--   D. García-Soriano and A. Miyauchi, Hermite Brings a Laptop, https://arxiv.org/abs/2609.35453, §2.3, Eq. (9), and Proposition 4.4 (p. 29 of the mission version). The explicit degree-20 numerators form a certificate constructed for that proposition by Gaussian moment recurrence.

import Definitions.Def_HermiteLaptop_MaxAgree_Hermite

namespace HermiteLaptop.MaxAgree
theorem four_spoke_degree20_lower_bounds (m : ℕ) (hm : m ≤ 20) :
  (((([250000, 353204, 101321, 38488, 37526, 17395, 19263, 11063, 11857, 7898, 8181,
    5988, 6079, 4729, 4749, 3850, 3845, 3210, 3197, 2728, 2713] : List ℕ)[m]?.getD 0 : ℕ) : ℝ)) / 1000000 ≤ coeffC 4 m := by sorry
end HermiteLaptop.MaxAgree

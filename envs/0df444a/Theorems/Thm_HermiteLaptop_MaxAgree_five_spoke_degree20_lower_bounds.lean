-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_five_spoke_degree20_lower_bounds
-- name    : HermiteLaptop.MaxAgree.five_spoke_degree20_lower_bounds
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-18T15:19:17.254193+00:00
-- url     : https://prove2.me/theorems/a8c68df9-996a-4c93-b863-ddf79115a0f7
-- title:
--   Degree-20 Hermite coefficient lower bounds for five-spoke rounding
-- statement:
--   For five-spoke Gaussian argmax rounding, let $c_{5,m}$ denote the sum over all winning coordinates of the squared Hermite coefficients of total degree $m$. For each $0\le m\le20$, the coefficient satisfies
--   $$c_{5,m}\ge L_m/10^6.$$
--   The integers $L_0,\ldots,L_{20}$, in order of degree, are
--
--   200000, 338121, 133340, 36608, 44451, 19403, 21276, 13169, 12703, 9536, 8708, 7209, 6493, 5651, 5104, 4567, 4158, 3784, 3476, 3199, 2962.
-- source:
--   D. García-Soriano and A. Miyauchi, Hermite Brings a Laptop, https://arxiv.org/abs/2609.35453, §2.3, Eq. (9), and Proposition 4.4 (p. 29 of the mission version). The explicit degree-20 numerators form a certificate constructed for that proposition by Gaussian moment recurrence.

import Definitions.Def_HermiteLaptop_MaxAgree_Hermite

namespace HermiteLaptop.MaxAgree
theorem five_spoke_degree20_lower_bounds (m : ℕ) (hm : m ≤ 20) :
  (((([200000, 338121, 133340, 36608, 44451, 19403, 21276, 13169, 12703, 9536, 8708,
    7209, 6493, 5651, 5104, 4567, 4158, 3784, 3476, 3199, 2962] : List ℕ)[m]?.getD 0 : ℕ) : ℝ)) / 1000000 ≤ coeffC 5 m := by sorry
end HermiteLaptop.MaxAgree

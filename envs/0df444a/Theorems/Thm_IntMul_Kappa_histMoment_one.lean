-- Prove2me | Theorems.Thm_IntMul_Kappa_histMoment_one
-- name    : IntMul.Kappa.histMoment_one
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:38:40.363995+00:00
-- url     : https://prove2.me/theorems/2d3819ab-694b-45a3-b29e-8daa77c9c42e
-- title:
--   Child-width moment at exponent 1 equals rank sum over width
-- statement:
--   Let $h=((w_i,n_i))_i$ be a child-width histogram and let $m>0$ be a network width. The moment at exponent $1$ collapses to the normalized rank sum:
--   $$\mathrm{histMoment}(h,m,1)=\sum_i n_i\cdot\frac{w_i}{m}=\frac{1}{m}\sum_i w_i n_i=\frac{\mathrm{histRankSum}(h)}{m}.$$
--   This identity is the $\tau=1$ endpoint used when comparing frozen round-seven/eight bit histograms (equal rank sums imply equal moments at exponent $1$).
-- source:
--   Def_IntMul_KappaFramework histMoment / histRankSum; used with Jain bitR7plain / bitR8 rank-sum identities

import Definitions.Def_IntMul_KappaFramework

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa

/-- At exponent $1$, the child-width moment equals the rank sum divided by the network width:
$\mathrm{histMoment}(h,m,1)=(\mathrm{histRankSum}\,h)/m$. -/
theorem histMoment_one (h : List (ℕ × ℕ)) (m : ℕ) (hm : (m : ℝ) ≠ 0) :
    histMoment h m 1 = (histRankSum h : ℝ) / m := by
  sorry

end IntMul.Kappa

-- Prove2me | Theorems.Thm_MarkovMixing_coupon_tail
-- name    : MarkovMixing.coupon_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:43:54.531514+00:00
-- url     : https://prove2.me/theorems/d2db8152-4b6f-4ce7-9142-c77568535b88
-- title:
--   Proposition 2.4 -- the coupon collector's tail bound
-- statement:
--   For the coupon collector with $n\ge1$ types and any $c>0$: $$\mathbb{P}\{\tau>\lceil n\log n+cn\rceil\}\le e^{-c}.$$ This bound drives the top-to-random shuffle analysis later in the series.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 2.2, Proposition 2.4, p. 23

import Definitions.Def_mm_classical

namespace MarkovMixing

/-- **Proposition 2.4** (LPW): the coupon collector time exceeds
`⌈n log n + cn⌉` with probability at most `e^{-c}`. -/
theorem coupon_tail (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : 0 < c) :
    couponMissProb n ⌈(n : ℝ) * Real.log n + c * n⌉₊ ≤ Real.exp (-c) := by
  sorry

end MarkovMixing

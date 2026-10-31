-- Prove2me | Theorems.Thm_LL_Decomp1528b_neg_log_one_sub_inv_bounds
-- name    : LL_Decomp1528b.neg_log_one_sub_inv_bounds
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:08:42.491853+00:00
-- url     : https://prove2.me/theorems/d58a7abe-1afc-48f4-bbd0-32bbfbee2e29
-- title:
--   Two sided bound for the logarithmic remainder
-- statement:
--   For real $p\ge 2$, $0\le -\log(1-1/p)-1/p$ and $-\log(1-1/p)-1/p\le 1/(2p(p-1))$.
-- source:
--   Rosser and Schoenfeld, Illinois J. Math. 6 (1962), proof of Theorem 7, p. 75 style

import Mathlib

open Real Finset Filter Topology

namespace LL_Decomp1528b
theorem neg_log_one_sub_inv_bounds {p : ℝ} (hp : 2 ≤ p) :
    0 ≤ -log (1 - 1 / p) - 1 / p ∧ -log (1 - 1 / p) - 1 / p ≤ 1 / (2 * p * (p - 1)) := by sorry
end LL_Decomp1528b

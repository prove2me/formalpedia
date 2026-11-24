-- Prove2me | Theorems.Thm_LL_Feed1122DecompJ1235Split_leaf_recip_lt_one
-- name    : LL_Feed1122DecompJ1235Split.leaf_recip_lt_one
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T14:59:04.392297+00:00
-- url     : https://prove2.me/theorems/daa3a2af-7381-4049-b045-fad3b2ca27ba
-- title:
--   Reciprocal sum below one off the candidate list
-- statement:
--   For every natural number $L<8\,000\,000$ that is not in the list candidates, the rational sum $\sum 1/d$ over the divisors $d$ of $L$ with $d+1$ prime and $d\ge 4$ is strictly less than $1$.
-- source:
--   Erdős problem 273, https://www.erdosproblems.com/273, reciprocal test step of the covering search

import Mathlib
import Definitions.Def_LL_Feed1122DecompJ1235Split_candidates

namespace LL_Feed1122DecompJ1235Split
theorem leaf_recip_lt_one (L : ℕ) (hL : L < 8000000) (hC : L ∉ candidates) :
    (∑ d ∈ (Nat.divisors L).filter (fun d => (d + 1).Prime ∧ 4 ≤ d), (1 : ℚ) / d) < 1 := by sorry
end LL_Feed1122DecompJ1235Split

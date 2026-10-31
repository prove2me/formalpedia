-- Prove2me | Theorems.Thm_LL_Decomp1526a_rep_le_log_sq_mul_gcount
-- name    : LL_Decomp1526a.rep_le_log_sq_mul_gcount
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:04:34.771988+00:00
-- url     : https://prove2.me/theorems/3f579a79-b68b-4c1c-a143-2a400a2dc6e6
-- title:
--   Weighted count bounded by unweighted count
-- statement:
--   For every natural number $N$, $r(N)\le(\log N)^2\,g(N)$, where $g(N)$ is the number of primes $p\le N$ with $N-p$ prime, cast to the reals.
-- source:
--   Halberstam and Richert, Sieve Methods, Ch. 3, passage from weighted to unweighted counts.

import Mathlib
import Definitions.Def_LL_Decomp1526a_rep
import Definitions.Def_LL_Decomp1526a_gcount

open Finset Real
open scoped Chebyshev Classical

namespace LL_Decomp1526a
theorem rep_le_log_sq_mul_gcount (N : ℕ) : rep N ≤ Real.log N ^ 2 * gcount N := by sorry
end LL_Decomp1526a

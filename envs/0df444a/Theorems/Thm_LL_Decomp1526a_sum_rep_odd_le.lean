-- Prove2me | Theorems.Thm_LL_Decomp1526a_sum_rep_odd_le
-- name    : LL_Decomp1526a.sum_rep_odd_le
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:05:59.164751+00:00
-- url     : https://prove2.me/theorems/a9fb4d98-82e6-4eec-8739-a8cec8dae885
-- title:
--   Odd arguments carry weight at most 2 log 2 times theta
-- statement:
--   For all natural numbers $a,b$, the sum of $r(N)$ over odd $N$ with $a<N\le b$ is at most $2\log 2\cdot\theta(b)$, where $\theta$ is the first Chebyshev function.
-- source:
--   Elementary; Ramaré 1995, Section 2.3, p. 653.

import Mathlib
import Definitions.Def_LL_Decomp1526a_rep

open Finset Real
open scoped Chebyshev Classical

namespace LL_Decomp1526a
theorem sum_rep_odd_le (a b : ℕ) :
    ∑ N ∈ (Ioc a b).filter (fun N => ¬ Even N), rep N ≤ 2 * Real.log 2 * θ (b : ℝ) := by sorry
end LL_Decomp1526a

-- Prove2me | Theorems.Thm_LL_Decomp1537b_ell_le
-- name    : LL_Decomp1537b.ell_le
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:33:18.39231+00:00
-- url     : https://prove2.me/theorems/a6be87b5-034e-46e7-9012-a34bea5beb78
-- title:
--   Size of the conductor logarithm
-- statement:
--   For real numbers $N,r,t$ with $N\ge4$, $1\le r\le N$ and $|t|\le\sqrt N$, one has $\log\bigl(r(|t|+2)\bigr)\le2\log N$.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem II, Acta Mathematica Hungarica, 2020; Section 2, displays (2.12) p. 3 and (2.30) p. 6

import Mathlib

open Finset Real

namespace LL_Decomp1537b
theorem ell_le {N r t : ℝ} (hN : 4 ≤ N) (hr : 1 ≤ r) (hrN : r ≤ N) (ht : |t| ≤ Real.sqrt N) :
    Real.log (r * (|t| + 2)) ≤ 2 * Real.log N := by sorry
end LL_Decomp1537b

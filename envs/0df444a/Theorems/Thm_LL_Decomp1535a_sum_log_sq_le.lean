-- Prove2me | Theorems.Thm_LL_Decomp1535a_sum_log_sq_le
-- name    : LL_Decomp1535a.sum_log_sq_le
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:12:20.612949+00:00
-- url     : https://prove2.me/theorems/da798753-37df-45af-8885-be9e0c110d05
-- title:
--   Sum of squared logs below log N times theta
-- statement:
--   For every natural number $N$, $\sum_{p\le N,\ p\text{ prime}}(\log p)^2\le \log N\cdot\theta(N)$.
-- source:
--   Liu and Wang 2002, p. 174, proof of Theorem 1

import Mathlib
import Definitions.Def_LL_Decomp1535a_theta

open MeasureTheory

namespace LL_Decomp1535a
theorem sum_log_sq_le (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 ≤
      Real.log N * theta N := by sorry
end LL_Decomp1535a

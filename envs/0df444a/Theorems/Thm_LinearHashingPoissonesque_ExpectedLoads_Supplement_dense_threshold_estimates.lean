-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_Supplement_dense_threshold_estimates
-- name    : LinearHashingPoissonesque.ExpectedLoads.Supplement.dense_threshold_estimates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:08:23.19475+00:00
-- url     : https://prove2.me/theorems/c87ead77-ae85-4936-b9fa-4932d9cee45a
-- title:
--   Proposition 2 (used in the proof of Theorem 10) — dense threshold estimates
-- statement:
--   Let $m>0$ be real and $1\le r\le n$ be integers. Set $\mu=m/n$ and assume $\log(n/r)\le\mu$. Both dense-regime estimates hold:
--
--   $$T_r^+(m,n)\le\mu+2\sqrt{\mu\log(n/r)},\qquad
--   T_r^-(m,n)\ge\mu-\sqrt{2\mu\log(n/r)}.$$
--
--   The constants $2$ outside the first square root and $2$ inside the second square root are distinct and exact. These estimates support Theorem 10, and apply to arbitrary positive $n$, without a power-of-two restriction.
--
--   Differences from the source:
--   - encoding: Definition 1 real Poisson thresholds → published upperThreshold and lowerThreshold, using their root sets and exact zero branch; reason: on positive real m and 1 ≤ r ≤ n the nonzero root sets are singletons; no rounding or extra hypothesis is imposed
--   - encoding: the two threshold inequalities with mu=m/n → a conjunction with mu substituted and n,r natural; reason: 1 ≤ r ≤ n implies n ≥ 1; m remains real and no power-of-two constraint is imposed
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.19, Proposition 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf#page=19

import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_PoissonThresholds

namespace LinearHashingPoissonesque.ExpectedLoads.Supplement

/-- Proposition 2, p.19: arbitrary positive real m and arbitrary 1 ≤ r ≤ n. -/
theorem dense_threshold_estimates (m : ℝ) (n r : ℕ) (hm : 0 < m)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hdense : Real.log ((n : ℝ) / r) ≤ m / n) :
    upperThreshold m n r ≤ m / n + 2 * Real.sqrt (m / n * Real.log ((n : ℝ) / r)) ∧
    m / n - Real.sqrt (2 * (m / n) * Real.log ((n : ℝ) / r)) ≤
      lowerThreshold m n r := by sorry

end LinearHashingPoissonesque.ExpectedLoads.Supplement

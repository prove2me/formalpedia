-- Prove2me | Theorems.Thm_JohnsonApprox_ExactCover_one_add_log_le_harmonic_add_half
-- name    : JohnsonApprox.ExactCover.one_add_log_le_harmonic_add_half
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:33:47.111588+00:00
-- url     : https://prove2.me/theorems/2b2438a0-80af-46d0-b366-b6da66abcfc2
-- title:
--   Theorem 6 — the inequality 1 + ln(k) ≤ Σ_{j=1}^k (1/j) + 1/2
-- statement:
--   For every integer $k \ge 1$,
--   $$1 + \ln(k) \le \sum_{j=1}^{k} \frac{1}{j} + \frac{1}{2}.$$
--
--   This is the second inequality in the display of Theorem 6. It shows that C2's guarantee $1 + \ln k$ on EC$(k)$ exceeds the guarantee $\sum_{j=1}^k 1/j$ of the greedy algorithm C1 on SC$(k)$ by less than $1/2$.
--
--   **Formalization Note** $\sum_{j=1}^k 1/j$ is Mathlib's `harmonic k` (a rational), cast to the reals; $\ln$ is `Real.log`.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 271, Theorem 6

import Mathlib

namespace JohnsonApprox.ExactCover

/-- Theorem 6 (p. 271), the analytic inequality of the display: `1 + ln(k) ≤ Σ_{j=1}^k (1/j) + 1/2`
for all `k ≥ 1`. -/
theorem one_add_log_le_harmonic_add_half (k : ℕ) (hk : 1 ≤ k) :
    1 + Real.log k ≤ (harmonic k : ℝ) + 1 / 2 := by sorry

end JohnsonApprox.ExactCover

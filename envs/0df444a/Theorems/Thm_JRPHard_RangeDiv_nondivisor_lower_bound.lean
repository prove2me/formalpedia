-- Prove2me | Theorems.Thm_JRPHard_RangeDiv_nondivisor_lower_bound
-- name    : JRPHard.RangeDiv.nondivisor_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:05:03.648734+00:00
-- url     : https://prove2.me/theorems/c67e3284-31b1-4c64-9c0d-dfcdca861406
-- title:
--   Proof of Lemma 3, p. 14 — a period q with gcd(q, M) ≠ q has objective at least 2√(2LU) > L + U
-- statement:
--   Let $M \ge U \ge L > 0$ be integers with $L + U < 2\sqrt{2LU}$, and let $q$ be a positive integer with $\gcd(q, M) \ne q$ (that is, $q$ does not divide $M$). Then the objective of problem (5) at $q$ satisfies
--   $$\frac{LU}{\gcd(q,M)} + q \ \ge\ 2\sqrt{2LU} \qquad\text{and}\qquad \frac{LU}{\gcd(q,M)} + q \ >\ L + U.$$
--
--   So a period that does not divide $M$ never reaches the level $L + U$; this is where RangeDivisor's condition $L + U < 2\sqrt{2LU}$ is used.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 14, §3.1, proof of Lemma 3, display "min_{q>0} 2K₀/q + q ≥ 2√(2K₀) = 2√(2LU) > L + U"

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting

namespace JRPHard.RangeDiv

theorem nondivisor_lower_bound (M L U : ℕ) (hI : IsRangeDivisorInstance M L U) (q : ℕ)
    (hq : 0 < q) (hne : Nat.gcd q M ≠ q) :
    2 * Real.sqrt (2 * (L : ℝ) * U) ≤ obj5 M L U q ∧ (L : ℝ) + U < obj5 M L U q := by sorry

end JRPHard.RangeDiv

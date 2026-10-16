-- Prove2me | Theorems.Thm_JRPHard_Periodic_small_divisor_value
-- name    : JRPHard.Periodic.small_divisor_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:41.012699+00:00
-- url     : https://prove2.me/theorems/a803eb26-a337-48a0-af1e-b22d5357884c
-- title:
--   Proof of Lemma 2, p. 11 — for such a divisor p, M/gcd(p, M) + p ≤ 2M/3
-- statement:
--   Let $M$ and $p$ be natural numbers with $p \mid M$, $3 \le p$ and $3p \le M$. Then the objective of problem (4) at $p$ satisfies
--   $$\frac{M}{\gcd(p,M)} + p \le \frac{2M}{3}.$$
--
--   Together with the existence of such a divisor for odd composite $M$, this shows that the optimal value of problem (4) is at most $2M/3$, strictly below $M$.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 11, §2.2, proof of Lemma 2, "Optimal replenishment cycle for item 1", last sentence of p. 11

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting

namespace JRPHard.Periodic

theorem small_divisor_value (M p : ℕ) (hpM : p ∣ M) (hp3 : 3 ≤ p) (hple : 3 * p ≤ M) :
    obj4 M p ≤ 2 * (M : ℝ) / 3 := by sorry

end JRPHard.Periodic

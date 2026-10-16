-- Prove2me | Theorems.Thm_JRPHard_RangeDiv_gcd_le_half
-- name    : JRPHard.RangeDiv.gcd_le_half
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:59.438068+00:00
-- url     : https://prove2.me/theorems/122f0564-6990-451b-9f45-c5f20bba6760
-- title:
--   Proof of Lemma 3, p. 14 — if gcd(q, M) ≠ q then gcd(q, M) ≤ q/2
-- statement:
--   Let $M$ be a natural number and $q$ a positive integer. If $\gcd(q, M) \ne q$, then
--   $$\gcd(q, M) \le \frac{q}{2}.$$
--
--   The greatest common divisor is a divisor of $q$; a divisor of $q$ other than $q$ itself is at most $q/2$. This is what separates non-divisors of $M$ from divisors in problem (5).
--
--   **Formalization Note** The bound is stated without division, as $2\gcd(q,M) \le q$ in the natural numbers.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 14, §3.1, proof of Lemma 3, "Note that for any integer q satisfying gcd(q, M) ≠ q"

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting

namespace JRPHard.RangeDiv

theorem gcd_le_half (M q : ℕ) (hq : 0 < q) (hne : Nat.gcd q M ≠ q) :
    2 * Nat.gcd q M ≤ q := by sorry

end JRPHard.RangeDiv

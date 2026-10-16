-- Prove2me | Theorems.Thm_JRPHard_RangeDiv_cheap_divisor_in_range
-- name    : JRPHard.RangeDiv.cheap_divisor_in_range
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:55.884604+00:00
-- url     : https://prove2.me/theorems/315c6f0b-8ed6-424e-89c8-cbfde3b69057
-- title:
--   Proof of Lemma 3, p. 15 — a period with objective at most L + U divides M and lies in [L, U]
-- statement:
--   Let $M \ge U \ge L > 0$ be integers with $L + U < 2\sqrt{2LU}$, and let $q$ be a positive integer with
--   $$\frac{LU}{\gcd(q,M)} + q \ \le\ L + U.$$
--   Then $q$ divides $M$, and $L \le q \le U$.
--
--   This is the "no-instance" direction of the reduction: if problem (5) reaches the level $L + U$, the period achieving it is a divisor of $M$ in the range $[L, U]$.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 15, §3.1, proof of Lemma 3, "On the other hand, if JRP_{M,U,L} ≤ L + U, then the optimizer must be a divisor of M"

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting

namespace JRPHard.RangeDiv

theorem cheap_divisor_in_range (M L U : ℕ) (hI : IsRangeDivisorInstance M L U) (q : ℕ)
    (hq : 0 < q) (hle : obj5 M L U q ≤ (L : ℝ) + U) :
    q ∣ M ∧ L ≤ q ∧ q ≤ U := by sorry

end JRPHard.RangeDiv

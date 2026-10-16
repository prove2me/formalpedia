-- Prove2me | Theorems.Thm_JRPHard_RangeDiv_divisor_in_range_cheap
-- name    : JRPHard.RangeDiv.divisor_in_range_cheap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:05:24.04845+00:00
-- url     : https://prove2.me/theorems/b1695e34-52a3-4658-ac67-c8d6850ae931
-- title:
--   Proof of Lemma 3, p. 15 — a divisor q of M in [L, U] has objective at most L + U
-- statement:
--   Let $M \ge U \ge L > 0$ be integers with $L + U < 2\sqrt{2LU}$. If $q$ divides $M$ and $L \le q \le U$, then
--   $$\frac{LU}{\gcd(q,M)} + q \ \le\ L + U.$$
--
--   This is the "yes-instance" direction of the reduction: a divisor in the range yields a cheap period for item 1.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 15, §3.1, proof of Lemma 3, "Now, suppose there exists q in [L, U] dividing M"

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting

namespace JRPHard.RangeDiv

theorem divisor_in_range_cheap (M L U : ℕ) (hI : IsRangeDivisorInstance M L U) (q : ℕ)
    (hdvd : q ∣ M) (hL : L ≤ q) (hU : q ≤ U) :
    obj5 M L U q ≤ (L : ℝ) + U := by sorry

end JRPHard.RangeDiv

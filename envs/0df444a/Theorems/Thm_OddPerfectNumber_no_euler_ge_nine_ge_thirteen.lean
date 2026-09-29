-- Prove2me | Theorems.Thm_OddPerfectNumber_no_euler_ge_nine_ge_thirteen
-- name    : OddPerfectNumber.no_euler_ge_nine_ge_thirteen
-- status  : Open
-- author  : @WillR
-- created : 2026-09-10T22:28:13.626063+00:00
-- url     : https://prove2.me/theorems/f71b7e50-3b42-4786-8b09-09cbc162a707
-- title:
--   Euler equation with special exponent k ge 13 has no solution
-- statement:
--   Let p be prime with p congruent 1 mod 4, k congruent 1 mod 4 with k >= 13, m odd with p not dividing m. Then sigma(p^k) sigma(m^2) != 2 p^k m^2. Tail case covering all k >= 9 except k = 9.
-- source:
--   Euler structure theorem; Odd Perfect Number Conjecture mission, special-exponent tail k >= 13.

import Mathlib

namespace OddPerfectNumber

theorem no_euler_ge_nine_ge_thirteen (p k m : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m) :
    (∑ d ∈ (p ^ k).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d) != 2 * (p ^ k * m ^ 2) := by
  sorry

end OddPerfectNumber

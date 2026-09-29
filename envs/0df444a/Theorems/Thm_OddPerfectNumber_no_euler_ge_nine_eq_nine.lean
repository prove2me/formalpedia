-- Prove2me | Theorems.Thm_OddPerfectNumber_no_euler_ge_nine_eq_nine
-- name    : OddPerfectNumber.no_euler_ge_nine_eq_nine
-- status  : Open
-- author  : @WillR
-- created : 2026-09-10T22:28:29.026249+00:00
-- url     : https://prove2.me/theorems/ed9f4aca-3e8e-43ae-a13e-512bda51c870
-- title:
--   Euler equation with special exponent k = 9 has no solution
-- statement:
--   Let p be prime with p congruent 1 mod 4 and m odd with p not dividing m. For exponent k = 9, sigma(p^k) sigma(m^2) != 2 p^k m^2. First case of k congruent 1 mod 4 with k >= 9.
-- source:
--   Euler structure theorem; Odd Perfect Number Conjecture mission, special-exponent case k >= 9, first subcase.

import Mathlib

namespace OddPerfectNumber

theorem no_euler_ge_nine_eq_nine (p k m : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hk4 : k % 4 = 1) (hk9 : k = 9) (hm : Odd m) (hpm : ¬ p ∣ m) :
    (∑ d ∈ (p ^ k).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d) != 2 * (p ^ k * m ^ 2) := by
  sorry

end OddPerfectNumber

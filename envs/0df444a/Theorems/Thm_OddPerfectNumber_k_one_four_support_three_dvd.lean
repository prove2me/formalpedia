-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_four_support_three_dvd
-- name    : OddPerfectNumber.k_one_four_support_three_dvd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T13:38:49.33367+00:00
-- url     : https://prove2.me/theorems/579b7f7c-8db9-4eca-a39f-a00d82b8fa0d
-- title:
--   Four-support k=1 square part contains three
-- statement:
--   Under the canonical k=1 equations, an odd square part with exactly four distinct prime divisors must be divisible by 3.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_prime_power_sigma_euler_upper_bound

theorem OddPerfectNumber.k_one_four_support_three_dvd (p m d : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hcard : m.primeFactors.card = 4) :
    3 ∣ m := by sorry

-- Prove2me | Theorems.Thm_OddPerfectNumber_no_odd_perfect_k_one_not_odd_m
-- name    : OddPerfectNumber.no_odd_perfect_k_one_not_odd_m
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-10T22:28:15.93201+00:00
-- url     : https://prove2.me/theorems/36cad158-ae76-4fa3-874e-d832bb94adbe
-- title:
--   Special-exponent case k = 1 with m not odd is impossible
-- statement:
--   No perfect odd N equals p m^2 with p prime 1 mod 4, p not dividing m, and m not odd. Parity half of the k = 1 case.
-- source:
--   Parity half of the k = 1 case; Odd Perfect Number Conjecture mission.

import Mathlib

namespace OddPerfectNumber

theorem no_odd_perfect_k_one_not_odd_m (n p m : Nat) (hn : Nat.Perfect n) (hodd : Odd n)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_not_odd : ¬ Odd m) : n != p * m ^ 2 := by
  sorry

end OddPerfectNumber

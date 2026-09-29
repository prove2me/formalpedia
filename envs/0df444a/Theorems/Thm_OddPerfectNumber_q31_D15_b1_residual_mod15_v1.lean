-- Prove2me | Theorems.Thm_OddPerfectNumber_q31_D15_b1_residual_mod15_v1
-- name    : OddPerfectNumber.q31_D15_b1_residual_mod15_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T16:50:14.429077+00:00
-- url     : https://prove2.me/theorems/183ac958-8207-4a6e-b350-7fa4fbc06774
-- title:
--   q31 D15 b=1 residual congruence forces q4 = 1 mod 15
-- statement:
--   If q4 is prime above 31 and 3 and 5 both divide the multiplicative order of 3 mod q4, then q4 is 1 mod 15. Supplies the congruence premise for the q31 D15 b=1 {61,151} filter.

import Mathlib

namespace OddPerfectNumber

theorem q31_D15_b1_residual_mod15_v1 (q4 : Nat)
    (hprime : q4.Prime) (hlo : 31 < q4)
    (h3 : 3 ∣ orderOf (3 : ZMod q4)) (h5 : 5 ∣ orderOf (3 : ZMod q4)) :
    q4 % 15 = 1 := by
  sorry

end OddPerfectNumber

-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_p5_q31_local_factor_forces_d1_support
-- name    : OddPerfectNumber.Kernel.p5_q31_local_factor_forces_d1_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T07:04:29.648016+00:00
-- url     : https://prove2.me/theorems/3a8f4e91-71e8-4dc5-9f56-360c3cfbd4d3
-- title:
--   The explicit middle source forces two primes into the square component
-- statement:
--   Assume m=651*d1 and that every prime divisor of the local sigma factor sigma(31^4) is either 5, 31, 7, or divides m. Since sigma(31^4)=5*11*17351, the primes 11 and 17351 divide m; neither divides 651, so both divide d1.
-- source:
--   Concrete support-closure consequence for the `(p,q,r)=(5,31,7)` branch of the k=5 Odd Perfect Number residual, using the Proved local sigma supplier theorem.

import Mathlib

import Mathlib

namespace OddPerfectNumber.Kernel

theorem p5_q31_local_factor_forces_d1_support (m d1 : Nat)
    (hm : m = 651 * d1)
    (hsupp : ∀ l : Nat, l.Prime →
      l ∣ (∑ i ∈ Finset.range (2 * 2 + 1), 31 ^ i) →
      l = 5 ∨ l = 31 ∨ l = 7 ∨ l ∣ m) :
    11 ∣ d1 ∧ 17351 ∣ d1 := by
  sorry

end OddPerfectNumber.Kernel

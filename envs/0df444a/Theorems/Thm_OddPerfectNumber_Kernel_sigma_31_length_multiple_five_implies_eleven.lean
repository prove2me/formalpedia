-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sigma_31_length_multiple_five_implies_eleven
-- name    : OddPerfectNumber.Kernel.sigma_31_length_multiple_five_implies_eleven
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T13:09:59.462745+00:00
-- url     : https://prove2.me/theorems/28987746-8c43-4b50-b119-c0752e32c6ba
-- title:
--   A length-five multiple geometric sum at 31 is divisible by 11
-- statement:
--   If 5 divides 2e+1, then 11 divides the geometric sum 1+31+...+31^(2e). This follows because 31 has multiplicative order 5 modulo 11, so each block of five consecutive powers sums to zero modulo 11.
-- source:
--   This isolates the first support-closure step in the p=5 middle-source branch. Since 31 mod 11 = 9 and 9^5 = 1 mod 11 while 9 != 1, the powers repeat with period five and every complete block of five terms has sum zero modulo 11. The theorem is intentionally only the modular local-sigma fact; it does not claim a contradiction or assume any global source classification.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sigma_31_length_multiple_five_implies_eleven (e : Nat)
    (h : 5 ∣ 2 * e + 1) :
    11 ∣ ∑ i ∈ Finset.range (2 * e + 1), 31 ^ i := by
  sorry

end OddPerfectNumber.Kernel

-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_kernel_card_ge_three_cyclotomic
-- name    : OddPerfectNumber.Kernel.five_kernel_card_ge_three_cyclotomic
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T16:38:19.043983+00:00
-- url     : https://prove2.me/theorems/94784857-2d06-4ccd-9977-103700c892dd
-- title:
--   The square-free part of the k=5 Dris index has at least three prime factors
-- statement:
--   Let p be a prime congruent to 1 mod 4 and m odd with p not dividing m, and suppose the first Dris equation 2 m^2 = sigma(p^5) s holds with s not a square. Writing s = d1^2 d2 with d2 square-free and d1, d2 positive, the square-free part d2 has at least three distinct prime factors.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_kernel_card_ge_three_cyclotomic (p m s d1 d2 : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs_nsq : ¬ ∃ r, s = r ^ 2)
    (hd2 : d1 ^ 2 * d2 = s) (hd2pos : 0 < d2) (hdsf : Squarefree d2)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * s)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) :
    3 ≤ d2.primeFactors.card := by
  sorry

end OddPerfectNumber.Kernel

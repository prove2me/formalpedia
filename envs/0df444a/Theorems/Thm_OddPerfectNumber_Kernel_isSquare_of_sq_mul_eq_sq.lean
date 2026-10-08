-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_isSquare_of_sq_mul_eq_sq
-- name    : OddPerfectNumber.Kernel.isSquare_of_sq_mul_eq_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T18:30:04.308119+00:00
-- url     : https://prove2.me/theorems/2de63ca9-5eca-413f-b49e-0032da65b6c1
-- title:
--   A square times S equals a square only if S is a square
-- statement:
--   If d^2 * S = y^2 with d and S nonzero, then S is a square. For every prime p, v_p(S) = v_p(y^2) - v_p(d^2) is a difference of two even numbers, hence even; the proved mission helper isSq_iff_even_factorization turns everywhere-even factorization into IsSquare. No coprimality hypothesis is needed. This is the square-cancellation step for the k=5 first Dris equation: with S = q*r*(p^2+p+1)*((p+1)/2*(p^2-p+1)) and d = d1, it yields exactly the square witness hsq required by five_two_prime_cyclotomic_primes_dvd_m.
-- source:
--   Square-cancellation bridge for the k=5 two-prime residual hsq step. Truth-audited by exhaustive check over d,S in [1,60)x[1,400). Strictly weaker (hence sound) unlike the disproved coprime_prime_mul_sq variant: the dropped coprimality is genuinely unneeded since v_p(S) = even - even.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem isSquare_of_sq_mul_eq_sq (d S y : Nat) (hd : d != 0) (hS : S != 0)
    (h : d ^ 2 * S = y ^ 2) :
    IsSquare S := by
  sorry

end OddPerfectNumber.Kernel

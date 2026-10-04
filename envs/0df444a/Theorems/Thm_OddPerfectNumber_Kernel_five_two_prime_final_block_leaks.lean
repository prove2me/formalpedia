-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_final_block_leaks
-- name    : OddPerfectNumber.Kernel.five_two_prime_final_block_leaks
-- status  : Open
-- author  : @WillR
-- created : 2026-10-04T10:37:33.814795+00:00
-- url     : https://prove2.me/theorems/becbcd13-dad8-4c45-92ee-5972d332a985
-- title:
--   In the k=5 two-prime branch the final-block index prime always leaks a prime that divides neither m nor p, q, r
-- statement:
--   Let p be prime, q < r primes with r dividing m, and suppose both k=5 Dris equations hold with index d1^2 q r in the factored cyclotomic form. Then the local factor sigma(r^(2 v_r(m))) has a prime divisor which is none of p, q, r and does not divide m. This is the form of the support-closure failure that is specific to the larger index prime, i.e. the one attached to the final cyclotomic block. Measured over every two-prime configuration with Euler prime below 60000 and d1 below 200 (398 configurations, arising from the only two admissible Euler primes p = 5 and p = 293), this never fails. By contrast the same statement for q fails in some configurations, so r is the special one: for p = 5 it leaks 331 out of sigma(31^2) = 993 = 3*331, and for p = 293 the block of r = 86143 leaks 31, 337 and 236773.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_final_block_leaks {p m d1 q r : Nat}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hrd : Dvd.dvd r m)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    exists l : Nat, l.Prime /\ Dvd.dvd l (∑ d ∈ (r ^ (2 * m.factorization r)).divisors, d) /\
      l != p /\ l != q /\ l != r /\ Not (Dvd.dvd l m) := by
  sorry

end OddPerfectNumber.Kernel

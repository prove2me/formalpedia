-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_two_prime_no_incoming_source_at_exponent_one
-- name    : OddPerfectNumber.Kernel.two_prime_no_incoming_source_at_exponent_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T00:02:02.988342+00:00
-- url     : https://prove2.me/theorems/e9d19b6c-7fea-4dd2-9261-c09207c797b2
-- title:
--   In the two-prime k=5 branch a prime occurring to exponent one in m cannot be an incoming source of the Euler prime
-- statement:
--   In the two-prime k=5 branch with Euler prime p, index d1 squared times q times r with q<r both prime and both different from 3, and the factored first Dris equation, no prime occurring to exponent exactly one in m can supply the prime p in its local divisor sum. The first Dris equation forces p to be 5 modulo 12 via the proved theorem five_two_prime_index_not_three_mod_twelve; a base equal to 1 modulo p forces p to divide 3; otherwise the proved theorem dvd_three_term_sum_mod_p_gives_one_mod_three forces p to be 1 modulo 3, contradicting p = 5 modulo 12.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem two_prime_no_incoming_source_at_exponent_one {p m d1 q r t : Nat}
    (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m)
    (hpm : Not (Dvd.dvd p m)) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hq3 : q != 3) (hr3 : r != 3)
    (ht : t.Prime) (htd : Dvd.dvd t m) (htp : t != p)
    (hte : m.factorization t = 1)
    (h1 : 2 * m ^ 2 =
      (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (hgeom : Dvd.dvd p (∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i)) :
    False := by
  sorry

end OddPerfectNumber.Kernel

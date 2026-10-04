-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_index_block_has_foreign_prime
-- name    : OddPerfectNumber.Kernel.five_two_prime_index_block_has_foreign_prime
-- status  : Open
-- author  : @WillR
-- created : 2026-10-04T07:03:41.243983+00:00
-- url     : https://prove2.me/theorems/1dfcfae3-39b3-4b18-9319-d58853a3123a
-- title:
--   In the k=5 two-prime branch the index prime's own divisor sum carries a prime outside p, q and r
-- statement:
--   Let p be prime, q < r primes, suppose q divides m and the second k=5 Dris equation sigma(m^2) = p^5 d1^2 q r holds. Then the local factor sigma(q^(2 v_q(m))) has a prime divisor that is none of p, q or r. Since sigma(m^2) is the product of those local factors over the primes dividing m, and the second equation says every prime dividing sigma(m^2) is p or divides d1 or is q or r, such a foreign prime must divide d1; and the first Dris equation forces supp(d1) to lie inside supp(m), so the leak must recur. Computation over every Euler prime below 40000 admitting a genuine two-prime square class gives exactly two such primes, p = 5 with (q,r) = (7,31) and p = 293 with (q,r) = (79,86143), and in both cases the index block leaks: 19 for sigma(7^2), 43 for sigma(79^2).

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_index_block_has_foreign_prime {p m d1 q r : Nat} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hm : Dvd.dvd q m)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    exists l : Nat, l.Prime /\ Dvd.dvd l (∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i) /\
      l != p /\ l != q /\ l != r := by
  sorry

end OddPerfectNumber.Kernel

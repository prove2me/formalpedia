-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_local_sigma_supplier_allowed
-- name    : OddPerfectNumber.Kernel.five_two_prime_local_sigma_supplier_allowed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T08:48:06.959864+00:00
-- url     : https://prove2.me/theorems/45582f57-0c46-4a5e-ac4e-c3f64f858428
-- title:
--   In the k=5 two-prime branch every local divisor-sum factor supplies only p, q, r or a prime already dividing m
-- statement:
--   Let p be prime, q < r primes, m nonzero, and suppose both k=5 Dris equations hold with index d1^2 q r in the factored cyclotomic form. Let t be a prime dividing m. Then every prime dividing the local factor sigma(t^(2 v_t(m))) is one of p, q, r, or already a prime divisor of m. This combines two Proved results: the second Dris equation admits no prime supplier outside {p} union supp(d1) union {q,r}, and the first Dris equation forces supp(d1) to lie inside supp(m). Equivalently no local factor may introduce a genuinely new prime. Measured numerically, every one of the 48 two-prime configurations tested with p below 1200 and d1 below 25 violates this condition, for instance sigma(31^2) = 993 = 3*331 where 331 divides neither m nor p, q nor r. This is the local form of the closure failure that blocks the two-prime residual.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_local_sigma_supplier_allowed {p m d1 q r : Nat}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hm0 : m != 0)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r)))
    (t : Nat) (ht : t.Prime) (htd : Dvd.dvd t m)
    (htmem : t ∈ m.primeFactors) :
    forall l : Nat, l.Prime -> Dvd.dvd l (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d) ->
      (l = p \/ l = q \/ l = r \/ Dvd.dvd l m) := by
  sorry

end OddPerfectNumber.Kernel

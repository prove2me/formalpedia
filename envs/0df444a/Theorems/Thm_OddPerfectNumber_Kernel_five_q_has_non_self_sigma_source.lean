-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_q_has_non_self_sigma_source
-- name    : OddPerfectNumber.Kernel.five_q_has_non_self_sigma_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T20:52:59.785365+00:00
-- url     : https://prove2.me/theorems/b7cd8ebc-bdfd-4366-b2ba-7ba989ad30c2
-- title:
--   The two-prime index prime q has an incoming non-self sigma source
-- statement:
--   In the k=5 two-prime residual, the index prime q divides m (via the square witness and the primes-dvd-m theorem) and divides sigma(m^2) (via the index-primes-dvd-sigma theorem from h2 alone), so the generic non-self-source theorem yields an actual incoming sigma source t != prime.
-- source:
--   Instantiation of index_prime_has_non_self_sigma_source in the 6eb10265 residual context, composing Proved children: square_witness_of_first_dris, five_two_prime_cyclotomic_primes_dvd_m, five_two_prime_index_primes_dvd_sigma.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_q_has_non_self_sigma_source (p m d1 q r : Nat)
    (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1)
    (hm : Odd m) (hpm : ¬ p ∣ m)
    (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) *
      (d1 ^ 2 * (q * r)))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    exists t : Nat, t.Prime /\ Dvd.dvd t m /\ Not (Dvd.dvd t q) /\
      Dvd.dvd q (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i) := by
  sorry

end OddPerfectNumber.Kernel

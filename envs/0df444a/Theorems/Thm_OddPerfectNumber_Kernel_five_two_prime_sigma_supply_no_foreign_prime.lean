-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_sigma_supply_no_foreign_prime
-- name    : OddPerfectNumber.Kernel.five_two_prime_sigma_supply_no_foreign_prime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T06:25:59.829372+00:00
-- url     : https://prove2.me/theorems/ef31275b-257f-4342-9862-c385df8d72b6
-- title:
--   The second Dris equation admits no prime supplier outside p, d1, q and r
-- statement:
--   Suppose the second k=5 Dris equation sigma(m^2) = p^5 * d1^2 * q * r holds with q and r prime. Then every prime dividing sigma(m^2) is one of p, a prime dividing d1, q, or r. This is the support-closure form of the second equation: once sigma is decomposed into local factors sigma(t^(2 v_t(m))) over the primes t dividing m, each local factor may carry only those four kinds of prime. Combined with the first equation, which forces the prime support of d1 to lie inside the support of m, this yields the self-referential closure condition that is the genuine obstruction in the two-prime branch.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_sigma_supply_no_foreign_prime {p m d1 q r : Nat} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    forall t : Nat, t.Prime -> Dvd.dvd t (∑ d ∈ (m ^ 2).divisors, d) ->
      (t = p \/ Dvd.dvd t d1 \/ t = q \/ t = r) := by
  sorry

end OddPerfectNumber.Kernel

-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_index_prime_has_odd_multiplicity_source
-- name    : OddPerfectNumber.Kernel.index_prime_has_odd_multiplicity_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T01:43:12.493596+00:00
-- url     : https://prove2.me/theorems/48e8fb88-535b-4892-98a3-54be43587354
-- title:
--   A fifth-power divisor with no sixth-power divisor has a source of odd multiplicity
-- statement:
--   Let m and p be natural numbers with p a prime dividing m, and suppose that the divisor sum of m squared is divisible by p to the fifth but not by p to the sixth. Then there is a prime t dividing m whose own divisor sum is divisible by p and moreover contains p to an odd multiplicity. The hypothesis that p to the sixth does not divide the divisor sum is what forces at least one local source to carry an odd multiplicity of p: if every local source carried an even multiplicity then the total multiplicity of p would be a multiple of six.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem index_prime_has_odd_multiplicity_source {m p : Nat} (hp : p.Prime)
    (hpm : Dvd.dvd p m) (hm2 : m ^ 2 != 0)
    (hpow : Dvd.dvd (p ^ 5) (∑ x ∈ (m ^ 2).divisors, x))
    (hn6 : Not (Dvd.dvd (p ^ 6) (∑ x ∈ (m ^ 2).divisors, x))) :
    exists t : Nat, Dvd.dvd t m /\ Dvd.dvd p (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i) /\
      Not (Even ((∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i).factorization p)) := by
  sorry

end OddPerfectNumber.Kernel

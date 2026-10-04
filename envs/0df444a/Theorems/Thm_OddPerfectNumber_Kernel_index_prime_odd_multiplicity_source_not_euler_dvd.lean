-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_index_prime_odd_multiplicity_source_not_euler_dvd
-- name    : OddPerfectNumber.Kernel.index_prime_odd_multiplicity_source_not_euler_dvd
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T10:29:11.117011+00:00
-- url     : https://prove2.me/theorems/9a610274-5ae3-4e0f-b518-a3bf4190c1be
-- title:
--   A fifth power dividing but not a sixth forces an odd-multiplicity local source
-- statement:
--   Let `m` and `p` be natural numbers with `p` prime, and suppose that the divisor sum of `m` squared is divisible by `p` to the fifth but not to the sixth. Then some prime `t` dividing `m` has a local geometric sum divisible by `p` carrying `p` to an odd multiplicity. This is the Euler-prime source statement needed by the k=5 two-prime residual, where the Euler prime provably does not divide `m`.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- Same content as `index_prime_has_odd_multiplicity_source` (48e8fb88) with the
hypothesis `p ∣ m` removed.  That hypothesis played no role in the accepted proof:
the extraction of an odd-multiplicity local sigma source needs only `p ^ 5 ∣ sigma(m ^ 2)`
and `¬ p ^ 6 ∣ sigma(m ^ 2)`.  In the hard residual `6eb10265` we have `¬ p ∣ m`, so the
published form cannot be instantiated there: the hypothesis is exactly the false one. -/
theorem index_prime_odd_multiplicity_source_not_euler_dvd {m p : Nat} (hp : p.Prime)
    (hm2 : m ^ 2 != 0) (hpow : Dvd.dvd (p ^ 5) (∑ x ∈ (m ^ 2).divisors, x))
    (hn6 : Not (Dvd.dvd (p ^ 6) (∑ x ∈ (m ^ 2).divisors, x))) :
    exists t : Nat, Dvd.dvd t m /\
      Dvd.dvd p (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i) /\
      Not (Even ((∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i).factorization p)) := by
  sorry

end OddPerfectNumber.Kernel

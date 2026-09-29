-- Prove2me | Theorems.Thm_OddPerfectNumber_sylvester_five_distinct_prime_factors
-- name    : OddPerfectNumber.sylvester_five_distinct_prime_factors
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-07T20:15:58.276398+00:00
-- url     : https://prove2.me/theorems/6b95fd6e-e047-4819-a171-9c496213d75a
-- title:
--   Sylvester: an odd perfect number has at least five distinct prime divisors
-- statement:
--   **Sylvester (1888).** If $N$ is odd and perfect, then $\omega(N) \ge 5$: $N$ has at least five distinct prime divisors.
--
--   The proof refines the abundancy estimate $\sigma(N)/N < \prod_{p \mid N} p/(p-1)$ by a case analysis over the possible small prime supports, using the multiplicativity of $\sigma$ and the constraints coming from Euler's form. Sylvester proved in the same work the stronger bound $\omega(N) \ge 8$ under the additional hypothesis $3 \nmid N$; the unconditional bound has since been improved to $\omega(N) \ge 8$ (Chein 1979, Hagis 1980), $\ge 9$ (Nielsen 2007) and $\ge 10$ (Nielsen 2015). Any of those stronger statements also settles this milestone.
--
--   Formalized with $\omega(N)$ as `N.primeFactors.card`.
-- source:
--   J. J. Sylvester, Sur les nombres parfaits, Comptes Rendus CVI (1888), 403-405; see also https://en.wikipedia.org/wiki/Perfect_number#Odd_perfect_numbers .

import Mathlib

namespace OddPerfectNumber

theorem sylvester_five_distinct_prime_factors (n : ℕ) (hn : Nat.Perfect n) (hodd : Odd n) :
    5 ≤ n.primeFactors.card := by
  sorry

end OddPerfectNumber

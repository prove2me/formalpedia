-- Prove2me | Theorems.Thm_OddPerfectNumber_nielsen_upper_bound
-- name    : OddPerfectNumber.nielsen_upper_bound
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-07T20:16:31.124858+00:00
-- url     : https://prove2.me/theorems/48e2876b-3d86-4067-8e62-3084a266a94e
-- title:
--   Nielsen: $N < 2^{4^{\omega(N)}}$ for an odd perfect number
-- statement:
--   **Nielsen's upper bound (2003).** If $N$ is an odd perfect number with $k = \omega(N)$ distinct prime divisors, then
--   $$N < 2^{4^{k}}.$$
--
--   The bound is doubly exponential in $k$, and it is the first result of its type: it makes the set of odd perfect numbers with a fixed number of distinct prime factors finite, hence in principle decidable by a finite (if astronomically large) computation. Combined with a lower bound on $\omega(N)$ it constrains the search region used in the computational work on the problem. Nielsen later sharpened the bound to $N < 2^{4^{k} - 2^{k}}$; a formalization of the sharper statement also settles this milestone.
--
--   Formalized with $\omega(N)$ as `N.primeFactors.card`.
-- source:
--   P. P. Nielsen, An upper bound for odd perfect numbers, INTEGERS: Electronic Journal of Combinatorial Number Theory 3 (2003), #A14, Theorem 1.

import Mathlib

namespace OddPerfectNumber

theorem nielsen_upper_bound (n : ℕ) (hn : Nat.Perfect n) (hodd : Odd n) :
    n < 2 ^ (4 ^ n.primeFactors.card) := by
  sorry

end OddPerfectNumber

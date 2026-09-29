-- Prove2me | Theorems.Thm_Gilbreath_row_one_eq_prime_gap
-- name    : Gilbreath.row_one_eq_prime_gap
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T16:49:09.687227+00:00
-- url     : https://prove2.me/theorems/7cb37cda-b18d-4f57-be9a-a7d9a10032fb
-- title:
--   Row $1$ is the sequence of prime gaps
-- statement:
--   The first row of the Gilbreath triangle is the sequence of prime gaps: $d^1(n) = p_{n+1} - p_n$ for every $n \ge 0$. The right-hand side is a subtraction of natural numbers, which is legitimate here because the enumeration of the primes is strictly increasing, so the absolute value in the definition of the triangle can be dropped at this level.
-- source:
--   Gilbreath's conjecture. N. L. Gilbreath (1958), as reported in R. B. Killgrove and K. E. Ralston, On a conjecture concerning the primes, MTAC 13 (1959), 121-122, https://doi.org/10.1090/S0025-5718-1959-0105398-3; A. M. Odlyzko, Iterated absolute values of differences of consecutive primes, Math. Comp. 61 (1993), 373-380, https://doi.org/10.1090/S0025-5718-1993-1192979-9; https://en.wikipedia.org/wiki/Gilbreath%27s_conjecture

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem row_one_eq_prime_gap (n : ℕ) :
    d 1 n = Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n := by sorry
end Gilbreath

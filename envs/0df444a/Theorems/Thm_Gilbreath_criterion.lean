-- Prove2me | Theorems.Thm_Gilbreath_criterion
-- name    : Gilbreath.criterion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T16:51:23.840615+00:00
-- url     : https://prove2.me/theorems/f819f6ad-bd3b-4fbc-bbc1-94ee63c7418b
-- title:
--   Reduction of Gilbreath's conjecture to blocks of $0$s and $2$s
-- statement:
--   The reduction underlying all computational work on the conjecture. Suppose that for every row index $K + 1$ there are $k \ge 1$ and $m$ with $k + m = K + 1$ such that row $k$ begins with $1$ and its entries at indices $1, \dots, m$ all lie in $\{0, 2\}$. Then Gilbreath's conjecture holds: $d^{K+1}(0) = 1$ for every $K$.
--
--   In words: it suffices that every row of the triangle be reachable from an earlier row that begins with $1$ and carries a block of entries in $\{0,2\}$ at least as long as the distance to be covered. The hypothesis is exactly what a computation establishes over a finite range; the conjecture is the assertion that it holds for all row indices.
-- source:
--   Gilbreath's conjecture. N. L. Gilbreath (1958), as reported in R. B. Killgrove and K. E. Ralston, On a conjecture concerning the primes, MTAC 13 (1959), 121-122, https://doi.org/10.1090/S0025-5718-1959-0105398-3; A. M. Odlyzko, Iterated absolute values of differences of consecutive primes, Math. Comp. 61 (1993), 373-380, https://doi.org/10.1090/S0025-5718-1993-1192979-9; https://en.wikipedia.org/wiki/Gilbreath%27s_conjecture

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem criterion
    (h : ∀ K : ℕ, ∃ k m : ℕ, 1 ≤ k ∧ k + m = K + 1 ∧ d k 0 = 1 ∧
      ∀ n, 1 ≤ n → n ≤ m → d k n = 0 ∨ d k n = 2) (K : ℕ) : d (K + 1) 0 = 1 := by sorry
end Gilbreath

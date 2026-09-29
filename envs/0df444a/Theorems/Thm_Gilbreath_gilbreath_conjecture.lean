-- Prove2me | Theorems.Thm_Gilbreath_gilbreath_conjecture
-- name    : Gilbreath.gilbreath_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T16:51:46.872747+00:00
-- url     : https://prove2.me/theorems/04fddea3-07af-43f9-a506-fe2207cda120
-- title:
--   Gilbreath's conjecture
-- statement:
--   **Gilbreath's conjecture.** Start from the increasing sequence of primes $p_0 = 2, p_1 = 3, p_2 = 5, \dots$ and repeatedly replace a row by the sequence of absolute differences of its consecutive entries:
--
--   $$ d^0(n) = p_n, \qquad d^{k+1}(n) = |d^k(n+1) - d^k(n)| . $$
--
--   Then every row after the first begins with $1$:
--
--   $$ d^k(0) = 1 \qquad \text{for all } k \ge 1 . $$
--
--   Observed by Norman L. Gilbreath in 1958 (and published, with a faulty proof, by François Proth in 1878), the statement has been verified for all row indices up to roughly $3.4 \times 10^{11}$ by Odlyzko (1993). No proof is known.
-- source:
--   Gilbreath's conjecture. N. L. Gilbreath (1958), as reported in R. B. Killgrove and K. E. Ralston, On a conjecture concerning the primes, MTAC 13 (1959), 121-122, https://doi.org/10.1090/S0025-5718-1959-0105398-3; A. M. Odlyzko, Iterated absolute values of differences of consecutive primes, Math. Comp. 61 (1993), 373-380, https://doi.org/10.1090/S0025-5718-1993-1192979-9; https://en.wikipedia.org/wiki/Gilbreath%27s_conjecture

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem gilbreath_conjecture (k : ℕ) : d (k + 1) 0 = 1 := by sorry
end Gilbreath

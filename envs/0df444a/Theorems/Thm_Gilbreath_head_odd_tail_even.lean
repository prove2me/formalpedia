-- Prove2me | Theorems.Thm_Gilbreath_head_odd_tail_even
-- name    : Gilbreath.head_odd_tail_even
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T16:50:34.796879+00:00
-- url     : https://prove2.me/theorems/29f31364-4f8a-4684-8d92-61ee12638ac4
-- title:
--   Every row after the primes starts odd and continues even
-- statement:
--   Parity structure of the Gilbreath triangle: for every $k \ge 1$ the leading entry $d^k(0)$ is odd and every later entry $d^k(n)$, $n \ge 1$, is even. The reason is that $p_0 = 2$ is the only even prime, so row $1$ starts with the odd number $1$ and continues with even gaps, and this parity pattern is reproduced by taking differences. In particular the leading entry of every row after the first is odd, hence nonzero — the conjecture is exactly the assertion that it is never larger than $1$.
-- source:
--   Gilbreath's conjecture. N. L. Gilbreath (1958), as reported in R. B. Killgrove and K. E. Ralston, On a conjecture concerning the primes, MTAC 13 (1959), 121-122, https://doi.org/10.1090/S0025-5718-1959-0105398-3; A. M. Odlyzko, Iterated absolute values of differences of consecutive primes, Math. Comp. 61 (1993), 373-380, https://doi.org/10.1090/S0025-5718-1993-1192979-9; https://en.wikipedia.org/wiki/Gilbreath%27s_conjecture

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem head_odd_tail_even (k : ℕ) :
    Odd (d (k + 1) 0) ∧ ∀ n : ℕ, Even (d (k + 1) (n + 1)) := by sorry
end Gilbreath

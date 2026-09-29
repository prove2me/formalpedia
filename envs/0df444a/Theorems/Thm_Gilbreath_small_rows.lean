-- Prove2me | Theorems.Thm_Gilbreath_small_rows
-- name    : Gilbreath.small_rows
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T16:43:14.995192+00:00
-- url     : https://prove2.me/theorems/17871081-c820-46f0-bb73-96336fcb179b
-- title:
--   Rows $1$ to $4$ of the Gilbreath triangle begin with $1$
-- statement:
--   A finite verification of Gilbreath's conjecture for the first four rows: for $1 \le k \le 4$ the leading entry $d^k(0)$ of row $k$ of the Gilbreath triangle equals $1$. Only the primes $p_0, \dots, p_4 = 2, 3, 5, 7, 11$ are involved, since the leading entry of row $k$ depends on the first $k+1$ entries of row $0$.
-- source:
--   Gilbreath's conjecture. N. L. Gilbreath (1958), as reported in R. B. Killgrove and K. E. Ralston, On a conjecture concerning the primes, MTAC 13 (1959), 121-122, https://doi.org/10.1090/S0025-5718-1959-0105398-3; A. M. Odlyzko, Iterated absolute values of differences of consecutive primes, Math. Comp. 61 (1993), 373-380, https://doi.org/10.1090/S0025-5718-1993-1192979-9; https://en.wikipedia.org/wiki/Gilbreath%27s_conjecture

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem small_rows (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) : d k 0 = 1 := by sorry
end Gilbreath

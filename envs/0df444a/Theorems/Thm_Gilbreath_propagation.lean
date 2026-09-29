-- Prove2me | Theorems.Thm_Gilbreath_propagation
-- name    : Gilbreath.propagation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T16:51:00.603609+00:00
-- url     : https://prove2.me/theorems/a11cadeb-9a7a-433b-bd81-94483198d701
-- title:
--   Propagation lemma: a leading $1$ followed by $0$s and $2$s persists
-- statement:
--   Odlyzko's propagation lemma, stated for an arbitrary sequence of natural numbers. Suppose $a(0) = 1$ and $a(n) \in \{0, 2\}$ for all $1 \le n \le m$. Then for every $j \le m$ the $j$-th iterated absolute-difference row of $a$ again begins with $1$: $(\Delta^j a)(0) = 1$.
--
--   The point is that the hypothesis is self-reproducing with one entry less of margin: if $a$ begins $1$ and continues in $\{0,2\}$ for $m$ entries, then $\Delta a$ begins $1$ and continues in $\{0,2\}$ for $m-1$ entries. A block of $m$ good entries therefore certifies the leading $1$ for the next $m$ rows, and nothing more. This is the mechanism behind every computational verification of Gilbreath's conjecture.
-- source:
--   Gilbreath's conjecture. N. L. Gilbreath (1958), as reported in R. B. Killgrove and K. E. Ralston, On a conjecture concerning the primes, MTAC 13 (1959), 121-122, https://doi.org/10.1090/S0025-5718-1959-0105398-3; A. M. Odlyzko, Iterated absolute values of differences of consecutive primes, Math. Comp. 61 (1993), 373-380, https://doi.org/10.1090/S0025-5718-1993-1192979-9; https://en.wikipedia.org/wiki/Gilbreath%27s_conjecture

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem propagation (a : ℕ → ℕ) (m : ℕ) (h0 : a 0 = 1)
    (h : ∀ n, 1 ≤ n → n ≤ m → a n = 0 ∨ a n = 2) (j : ℕ) (hj : j ≤ m) :
    iterAbsDiff a j 0 = 1 := by sorry
end Gilbreath

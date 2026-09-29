-- Prove2me | Theorems.Thm_Gilbreath_second_column
-- name    : Gilbreath.second_column
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:06:23.586698+00:00
-- url     : https://prove2.me/theorems/9b122789-850c-40e4-9ea8-39ab4c7a29b7
-- title:
--   The second column of the Gilbreath triangle is bounded by $2$
-- statement:
--   Row $k$ of the Gilbreath triangle is $d^k$, where $d^0(n) = p_n$ is the increasing enumeration of the primes and $d^{k+1}(n) = |d^k(n+1) - d^k(n)|$. This theorem asserts a bound on the **second column** of the triangle:
--
--   $$ d^{k}(1) \le 2 \qquad \text{for every } k \ge 1 . $$
--
--   Since every entry $d^k(n)$ with $k \ge 1$ and $n \ge 1$ is even (the mission milestone `Gilbreath.head_odd_tail_even`), the bound is equivalent to saying that the second column consists only of $0$s and $2$s, i.e. $d^k(1) \in \{0, 2\}$ for all $k \ge 1$. Numerically the rows begin
--
--   $$ 1\,2\,2\,4\,\dots,\qquad 1\,0\,2\,2\,\dots,\qquad 1\,2\,0\,0\,\dots,\qquad 1\,2\,0\,\dots, $$
--
--   so the second column starts $2, 0, 2, 2, \dots$.
--
--   The statement is exactly as strong as Gilbreath's conjecture, and it isolates the single column on which the conjecture depends. Indeed, by definition the head of a row is determined by the head and the second entry of the previous row,
--
--   $$ d^{k+1}(0) = \bigl| d^{k}(1) - d^{k}(0) \bigr| , $$
--
--   so if $d^k(0) = 1$ and $d^k(1) \in \{0,2\}$ then $d^{k+1}(0) = 1$. Starting from $d^1(0) = p_1 - p_0 = 1$, the bound above therefore propagates the leading $1$ through all rows and yields $d^k(0) = 1$ for every $k \ge 1$. Conversely, if every row begins with $1$ then $|d^k(1) - 1| = d^{k+1}(0) = 1$ forces $d^k(1) \in \{0, 2\}$, so the two statements are equivalent. Nothing weaker than the conjecture is being assumed, and nothing stronger: in particular no claim is made about the entries $d^k(n)$ with $n \ge 2$, which genuinely can exceed $2$ (for instance $d^1(3) = 11 - 7 = 4$).
--
--   **Formalization note.** The row index is written $k + 1$ so that the statement quantifies over the rows $1, 2, 3, \dots$; row $0$, the primes themselves, is excluded. Differences are formed in the integers and then taken in absolute value, so no truncated natural subtraction occurs.
-- source:
--   Gilbreath's conjecture; A. M. Odlyzko, Iterated absolute values of differences of consecutive primes, Math. Comp. 61 (1993), 373-380, https://doi.org/10.1090/S0025-5718-1993-1192979-9, Section 1; https://en.wikipedia.org/wiki/Gilbreath%27s_conjecture. Equivalent reformulation of the mission goal `Gilbreath.gilbreath_conjecture`, obtained from the recursion d^{k+1}(0) = |d^k(1) - d^k(0)| together with the parity milestone `Gilbreath.head_odd_tail_even`.

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem second_column (k : ℕ) : d (k + 1) 1 ≤ 2 := by sorry
end Gilbreath

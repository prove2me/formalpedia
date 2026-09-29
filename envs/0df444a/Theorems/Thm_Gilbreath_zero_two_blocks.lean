-- Prove2me | Theorems.Thm_Gilbreath_zero_two_blocks
-- name    : Gilbreath.zero_two_blocks
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:31:17.334116+00:00
-- url     : https://prove2.me/theorems/4e6e2458-bb2f-4e27-83b7-f950275a4e4b
-- title:
--   The rows of the Gilbreath triangle carry long initial blocks of $0$s and $2$s
-- statement:
--   Row $k$ of the Gilbreath triangle is $d^k$, where $d^0(n) = p_n$ is the increasing enumeration of the primes and $d^{k+1}(n) = |d^k(n+1) - d^k(n)|$. This theorem asserts that the rows of the triangle carry **initial blocks of $0$s and $2$s that are long enough to reach any prescribed row**:
--
--   $$ \text{for every } K \text{ there are } k \ge 1 \text{ and } m \text{ with } k + m = K + 1 \text{ such that } d^{k}(n) \in \{0, 2\} \text{ for all } 1 \le n \le m + 1 . $$
--
--   Only the entries of index $\ge 1$ are constrained; nothing is asserted about the leading entries $d^k(0)$, and nothing is asserted about the entries of index $> m + 1$, which genuinely can be large (for instance $d^1(3) = 11 - 7 = 4$, and far out in a row the entries reflect large prime gaps).
--
--   The reason this is the relevant statement is that the tail of the triangle is autonomous: for $n \ge 1$ the entry $d^{k+1}(n) = |d^{k}(n+1) - d^{k}(n)|$ involves only entries of index $\ge 1$. Since $\{0,2\}$ is closed under absolute differences, a block of $0$s and $2$s at the indices $1, \dots, m+1$ of row $k$ shortens by one index at each step but survives, so after $m$ steps one obtains $d^{K+1}(1) \in \{0, 2\}$. Because $d^{K+2}(0) = |d^{K+1}(1) - d^{K+1}(0)|$, this in turn propagates the leading $1$ of the triangle and yields Gilbreath's conjecture.
--
--   The statement is therefore equivalent to Gilbreath's conjecture: conversely, if every row begins with $1$ then $|d^{K+1}(1) - 1| = d^{K+2}(0) = 1$ gives $d^{K+1}(1) \in \{0,2\}$, so one may take $k = K+1$ and $m = 0$. What the reformulation buys is a change of shape. The leading column has been eliminated from both the hypothesis and the conclusion, so the problem is stated purely in terms of the even part of the triangle; dividing every entry by $2$, which is legitimate since all entries of index $\ge 1$ in rows $\ge 1$ are even, it becomes the assertion that the difference triangle built on the halved prime gaps $\tfrac{1}{2}(p_{n+2} - p_{n+1})$ acquires arbitrarily long initial blocks of $0$s and $1$s, at rows early enough to reach the target row.
--
--   **Formalization note.** The pair $(k, m)$ is quantified existentially with the constraint $k + m = K + 1$, which forces $k \le K + 1$ — the block must occur early enough to reach row $K + 1$ — and the block length $m + 1$ is at least $1$, so the case $k = K + 1$, $m = 0$ is the assertion $d^{K+1}(1) \in \{0,2\}$ itself. Differences are formed in the integers and then taken in absolute value, so no truncated natural subtraction occurs.
-- source:
--   Gilbreath's conjecture; A. M. Odlyzko, Iterated absolute values of differences of consecutive primes, Math. Comp. 61 (1993), 373-380, https://doi.org/10.1090/S0025-5718-1993-1192979-9, Section 1; https://en.wikipedia.org/wiki/Gilbreath%27s_conjecture. Equivalent reformulation of the mission goal Gilbreath.gilbreath_conjecture, obtained by removing the leading column from Gilbreath.second_column.

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem zero_two_blocks (K : ℕ) : ∃ k m : ℕ, 1 ≤ k ∧ k + m = K + 1 ∧
    ∀ n, 1 ≤ n → n ≤ m + 1 → d k n = 0 ∨ d k n = 2 := by sorry
end Gilbreath

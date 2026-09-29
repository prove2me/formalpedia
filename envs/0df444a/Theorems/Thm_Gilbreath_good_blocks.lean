-- Prove2me | Theorems.Thm_Gilbreath_good_blocks
-- name    : Gilbreath.good_blocks
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T19:26:43.178021+00:00
-- url     : https://prove2.me/theorems/e929e1c9-88cd-49c2-9942-4ddfe443b412
-- title:
--   Existence of blocks of $0$s and $2$s in the Gilbreath triangle
-- statement:
--   Gilbreath's conjecture is verified in practice by exhibiting, for each row index, an earlier row that begins with $1$ and is followed by a long block of entries in $\\{0, 2\\}$. This theorem is the assertion that such blocks always exist, in exactly the form required by the criterion.
--
--   Let $d^k$ denote row $k$ of the Gilbreath triangle: $d^0(n) = p_n$ is the increasing sequence of primes and $d^{k+1}(n) = |d^k(n+1) - d^k(n)|$. The claim is that for every natural number $K$ there are natural numbers $k$ and $m$ with
--
--   $$ k \\ge 1, \\qquad k + m = K + 1, \\qquad d^{k}(0) = 1, \\qquad d^{k}(n) \\in \\{0, 2\\} \\ \\text{ for all } 1 \\le n \\le m . $$
--
--   In words: the row $K+1$ that is to be certified can be reached from some earlier row $k$ that begins with $1$ and carries a block of entries in $\\{0,2\\}$ at least as long as the number $m = K + 1 - k$ of difference steps still to be taken.
--
--   This is the open content of Gilbreath's conjecture once the mechanical part has been isolated: combined with the propagation lemma, which shows that a row beginning with $1$ followed by $m$ entries in $\\{0,2\\}$ forces the leading entry $1$ for the next $m$ rows, it yields $d^{K+1}(0) = 1$ for every $K$. Odlyzko's computation establishes precisely this statement for all $K$ up to roughly $3.4 \\times 10^{11}$, by finding for each range a single row whose block of $0$s and $2$s is long enough. The case $K = 0$ is degenerate: one may take $k = 1$, $m = 0$, where the block condition is empty.
--
--   **Formalization Note** The row index $K+1$ is written with an explicit successor so that the statement quantifies over rows $1, 2, 3, \\dots$; row $0$ (the primes themselves) is excluded, as it is in the conjecture. Differences are formed in the integers and then taken in absolute value, so no truncated natural subtraction occurs.
-- source:
--   A. M. Odlyzko, Iterated absolute values of differences of consecutive primes, Math. Comp. 61 (1993), 373-380, https://doi.org/10.1090/S0025-5718-1993-1192979-9, Section 1 (the verification strategy: a row beginning with 1 followed by a block of 0s and 2s of length at least the number of remaining rows); see also https://en.wikipedia.org/wiki/Gilbreath%27s_conjecture. This is the hypothesis of the mission milestone `Gilbreath.criterion`.

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem good_blocks (K : ℕ) : ∃ k m : ℕ, 1 ≤ k ∧ k + m = K + 1 ∧ d k 0 = 1 ∧
    ∀ n, 1 ≤ n → n ≤ m → d k n = 0 ∨ d k n = 2 := by sorry
end Gilbreath

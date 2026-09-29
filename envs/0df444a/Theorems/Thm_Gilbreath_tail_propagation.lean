-- Prove2me | Theorems.Thm_Gilbreath_tail_propagation
-- name    : Gilbreath.tail_propagation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T20:31:29.398369+00:00
-- url     : https://prove2.me/theorems/63452029-c163-41f8-acb2-4e1294fc23d7
-- title:
--   Propagation of a $\{0,2\}$-block along the second column
-- statement:
--   For a sequence $a : \mathbb{N} \to \mathbb{N}$ write $(\Delta a)(n) = |a(n+1) - a(n)|$ and let $\Delta^j a$ be the $j$-fold iterate. This theorem is a propagation lemma for the **second column** of the difference triangle of $a$:
--
--   $$ \text{if } a(n) \in \{0, 2\} \text{ for all } 1 \le n \le j + 1, \quad\text{then}\quad (\Delta^{j} a)(1) \in \{0, 2\}. $$
--
--   The mechanism is that $\{0,2\}$ is closed under absolute differences, $|0-0| = |2-2| = 0$ and $|0-2| = |2-0| = 2$, so a block of $0$s and $2$s occupying the indices $1, \dots, m+1$ of a row produces a block of $0$s and $2$s occupying the indices $1, \dots, m$ of the next row: the block shortens by one index per step but never leaves $\{0,2\}$. After $j$ steps the index $1$ is still covered, which is the assertion above.
--
--   Two features distinguish this from Odlyzko's propagation lemma for the leading column (`Gilbreath.propagation`), which concludes $(\Delta^j a)(0) = 1$ from $a(0) = 1$ together with the same kind of block. First, no hypothesis whatsoever is placed on $a(0)$: the entries of the triangle at indices $\ge 1$ are computed from entries at indices $\ge 1$ only, so the tail of the triangle evolves autonomously and the leading column is irrelevant to it. Second, the conclusion concerns the column of index $1$ rather than the column of index $0$.
--
--   The statement is about an arbitrary sequence of natural numbers, not specifically about the primes; applied to a row $d^k$ of the Gilbreath triangle, and combined with $\Delta^{j} d^{k} = d^{k+j}$, it says that a block of $0$s and $2$s at the indices $1, \dots, m+1$ of row $k$ forces $d^{k+m}(1) \in \{0, 2\}$.
-- source:
--   Gilbreath's conjecture; A. M. Odlyzko, Iterated absolute values of differences of consecutive primes, Math. Comp. 61 (1993), 373-380, https://doi.org/10.1090/S0025-5718-1993-1192979-9, Section 1. Second-column analogue of the mission milestone Gilbreath.propagation.

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem tail_propagation (a : ℕ → ℕ) (j : ℕ)
    (h : ∀ n, 1 ≤ n → n ≤ j + 1 → a n = 0 ∨ a n = 2) :
    iterAbsDiff a j 1 = 0 ∨ iterAbsDiff a j 1 = 2 := by sorry
end Gilbreath

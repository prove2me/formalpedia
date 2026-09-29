-- Prove2me | Theorems.Thm_MagicSquares_comps_card
-- name    : MagicSquares.comps_card
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T18:23:30.812933+00:00
-- url     : https://prove2.me/theorems/65af2905-cd30-4bb9-aa15-3ea5f86790e0
-- title:
--   Stars and bars: the number of compositions of n into k parts
-- statement:
--   **Stars and bars.** The number of compositions of $n$ into
--   $k+1$ nonnegative parts is
--
--   $$\#\{x\in\mathbb{N}^{k+1} : x_{0}+\cdots+x_{k}=n\}=\binom{n+k}{n}.$$
--
--   This is the classical stars-and-bars count, stated in the boxed form used
--   throughout the mission: `comps N (k+1) n` is the finite set of functions
--   $\mathrm{Fin}(k+1)\to\mathrm{Fin}(N+1)$ whose values sum to $n$, and the
--   hypothesis $n\le N$ guarantees the box is inactive — every coordinate of such a
--   tuple is at most $n$, hence at most $N$.
--
--   **Proof.** Splitting off the first coordinate identifies compositions of $n$
--   into $k+2$ parts with the disjoint union, over $i=0,\dots,n$, of the
--   compositions of $n-i$ into $k+1$ parts; this gives the recurrence
--   $c(k+1,n)=\sum_{i\le n}c(k,n-i)$ with $c(0,n)=[n=0]$. The binomial
--   $\binom{n+k}{n}$ satisfies the same recurrence by the hockey-stick identity
--   $\sum_{j\le n}\binom{j+k}{j}=\binom{n+k+1}{n}$, which is itself an immediate
--   induction from Pascal's rule.
--
--   **Formalization Note** The count is taken inside a fixed box $\mathrm{Fin}(N+1)$
--   because $\mathbb{N}^{k}$ has no `Fintype`; holding $N$ fixed while $k$ and $n$
--   vary is what lets the induction avoid any reindexing of the tail.
-- source:
--   P. A. MacMahon, Combinatory Analysis (1915); M. Beck, T. Cohen, J. Cuomo, P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707-717; arXiv:math/0201013v3, Section 2, Theorem 1.

import Mathlib
import Definitions.Def_MagicSquaresCompositions
open MagicSquares

namespace MagicSquares

theorem comps_card (N k n : ℕ) (hn : n ≤ N) :
    (comps N (k + 1) n).card = (n + k).choose n := by sorry

end MagicSquares

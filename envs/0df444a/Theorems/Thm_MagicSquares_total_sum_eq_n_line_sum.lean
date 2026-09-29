-- Prove2me | Theorems.Thm_MagicSquares_total_sum_eq_n_line_sum
-- name    : MagicSquares.total_sum_eq_n_line_sum
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:06:05.039243+00:00
-- url     : https://prove2.me/theorems/426e247c-26f9-4b16-9c70-e541e809f3b1
-- title:
--   Total sum of a semi-magic square is n times the line sum
-- statement:
--   **Row-sum aggregation.** Let $A$ be an $n\times n$ array over an additive
--   commutative monoid, and suppose every row sums to the same value $S$ (a
--   *semi-magic square* of line sum $S$). Then the sum of **all** $n^{2}$ entries is
--
--   $$
--   \sum_{i}\sum_{j} A_{ij} \;=\; n\,S .
--   $$
--
--   Indeed the total is the sum of the $n$ row sums, each of which equals $S$. This
--   is the first structural identity of the theory: it is what converts the
--   *row* condition into a global constraint, and it is the reason the magic
--   constant of a normal magic square of order $n$ must be $n(n^{2}+1)/2$ — the
--   entries are $1,\dots,n^{2}$, whose total is $n^{2}(n^{2}+1)/2$, and dividing by
--   $n$ gives the line sum.
--
--   **Formalization Note** Entries live in an arbitrary `AddCommMonoid`, so the
--   statement reads $n\bullet S$ (`nsmul`) rather than $n\cdot S$; over $\mathbb{N}$
--   or a semiring the two coincide. Only the row half of `IsSemiMagic` is used.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717; arXiv:math/0201013v3.

import Mathlib
import Definitions.Def_MagicSquares

namespace MagicSquares

theorem total_sum_eq_n_line_sum {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsSemiMagic M s) :
    totalSum M = n • s := by sorry

end MagicSquares

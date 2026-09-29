-- Prove2me | Theorems.Thm_MagicSquares_flipVertical_preserves_magic
-- name    : MagicSquares.flipVertical_preserves_magic
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:06:11.211478+00:00
-- url     : https://prove2.me/theorems/9b89d44c-f278-4eb8-a8c2-b2513ecd1f12
-- title:
--   Vertical flip preserves magicness
-- statement:
--   **Vertical reflection.** Reversing the order of the rows of a magic square
--   again gives a magic square, with the same line sum.
--
--   The reflection $(i,j)\mapsto(n-1-i,\,j)$ sends rows to rows and columns to
--   columns, so every row and column of the reflected array is a row or column of the
--   original and sums to $S$. The two main diagonals are **interchanged**: the
--   descending diagonal of the reflected square is the ascending diagonal of the
--   original, and conversely. Since a magic square requires both diagonals to sum to
--   $S$, the reflected array satisfies all the conditions.
--
--   Together with the horizontal flip and the transpose, this generates the full
--   dihedral symmetry group of order $8$ of the square, under which the set of magic
--   squares of a fixed line sum is closed — the fact that makes "up to symmetry"
--   counts meaningful.
--
--   **Formalization Note** `flipVertical` reverses the row index via `Fin.rev`.
--   Column sums are invariant because $i\mapsto n-1-i$ permutes $\mathrm{Fin}\,n$, and
--   the diagonal swap is proved by the same reindexing.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717; arXiv:math/0201013v3.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresTransforms

namespace MagicSquares

theorem flipVertical_preserves_magic {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsMagic M s) :
    IsMagic (flipVertical M) s := by sorry

end MagicSquares

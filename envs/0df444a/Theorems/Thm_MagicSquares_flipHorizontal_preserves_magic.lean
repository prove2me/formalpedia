-- Prove2me | Theorems.Thm_MagicSquares_flipHorizontal_preserves_magic
-- name    : MagicSquares.flipHorizontal_preserves_magic
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:06:13.261956+00:00
-- url     : https://prove2.me/theorems/0bd2ee84-7eea-45d9-84fa-7c6f28595d84
-- title:
--   Horizontal flip preserves magicness
-- statement:
--   **Horizontal reflection.** Reversing the order of the columns of a magic square
--   again gives a magic square, with the same line sum.
--
--   This is the mirror image of the vertical flip: $(i,j)\mapsto(i,\,n-1-j)$ sends
--   columns to columns and rows to rows, and interchanges the two main diagonals. All
--   lines therefore still sum to $S$.
--
--   **Formalization Note** `flipHorizontal` reverses the column index via `Fin.rev`.
--   Row sums are invariant by reindexing; the two diagonals are swapped.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717; arXiv:math/0201013v3.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresTransforms

namespace MagicSquares

theorem flipHorizontal_preserves_magic {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsMagic M s) :
    IsMagic (flipHorizontal M) s := by sorry

end MagicSquares

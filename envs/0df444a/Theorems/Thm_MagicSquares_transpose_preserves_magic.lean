-- Prove2me | Theorems.Thm_MagicSquares_transpose_preserves_magic
-- name    : MagicSquares.transpose_preserves_magic
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:06:09.038019+00:00
-- url     : https://prove2.me/theorems/3b7c0d09-0acb-4754-97c7-068a27b91c00
-- title:
--   Transposing a magic square preserves magicness
-- statement:
--   **Transposition.** If $A$ is a magic square of line sum $S$, so is its
--   transpose $A^{\mathsf T}$, with the same line sum.
--
--   The square is a symmetry of the $n\times n$ grid, so it permutes the lines:
--   rows of $A^{\mathsf T}$ are the columns of $A$ and vice versa, while each main
--   diagonal is fixed. Hence every line of $A^{\mathsf T}$ is a line of $A$ and
--   still sums to $S$, and the same holds verbatim for panmagic (pandiagonal)
--   squares, whose broken diagonals are also carried to broken diagonals.
--
--   **Formalization Note** `transpose` is the entrywise flip $(i,j)\mapsto(j,i)$
--   from `Definitions.Def_MagicSquaresTransforms`. The four line sums are tracked by
--   `rowSum_transpose`, `colSum_transpose`, `diagSum_transpose` and
--   `antiDiagSum_transpose`; the anti-diagonal case uses that $i\mapsto n-1-i$ is a
--   bijection of $\mathrm{Fin}\,n$, so reindexing the sum is legitimate.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717; arXiv:math/0201013v3.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresTransforms

namespace MagicSquares

theorem transpose_preserves_magic {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsMagic M s) :
    IsMagic (transpose M) s := by sorry

end MagicSquares

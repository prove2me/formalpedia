-- Prove2me | Theorems.Thm_MagicSquares_center_of_order_three
-- name    : MagicSquares.center_of_order_three
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T12:11:42.650244+00:00
-- url     : https://prove2.me/theorems/ebbc5687-663f-472d-afb6-f760546652db
-- title:
--   The centre of a 3x3 magic square is one third of the line sum
-- statement:
--   In a $3 \times 3$ magic square the centre entry is
--   exactly one third of the magic constant.
--
--   Let $M$ be a $3 \times 3$ array of natural numbers whose three rows, three columns and two
--   main diagonals all sum to the same number $s$. Then
--
--   $$
--   3 \cdot M_{1,1} = s ,
--   $$
--
--   where $M_{1,1}$ is the central entry (indices are `Fin 3`, so the centre is the index $1$).
--
--   The proof is the classical one: add the middle row, the middle column and the two diagonals.
--   The centre is counted four times and every other cell exactly once, so the total is
--   $3s + 3M_{1,1}$; but it is also $4s$, whence $s = 3M_{1,1}$.
--
--   **Formalization Note** Everything stays in $\mathbb{N}$, so no divisibility hypothesis is
--   needed: the identity itself forces $3 \mid s$.
-- source:
--   Classical (Lo Shu); see Beck, Cohen, Cuomo & Gribelyuk, arXiv:math/0201013v3, Section 2, where the $3\times3$ magic square is parametrised by the centre entry $e$ with line sum $3e$.

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem center_of_order_three (M : Square 3 ℕ) (s : ℕ)
    (hM : IsMagic M s) :
    3 * M 1 1 = s := by sorry

end MagicSquares

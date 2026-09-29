-- Prove2me | Theorems.Thm_MagicSquares_magic_count_three_otherwise
-- name    : MagicSquares.magic_count_three_otherwise
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T12:11:42.767487+00:00
-- url     : https://prove2.me/theorems/fb4507f0-4ebd-432b-a1e7-e59697218d61
-- title:
--   No 3x3 magic square has a line sum coprime to 3
-- statement:
--   If $t$ is not divisible by $3$, there is no
--   $3 \times 3$ magic square with line sum $t$.
--
--   Write $M_{3}(t)$ for the number of $3 \times 3$ arrays of nonnegative integers whose three
--   rows, three columns and two main diagonals all sum to $t$. Then
--
--   $$
--   3 \nmid t \;\Longrightarrow\; M_{3}(t) = 0 .
--   $$
--
--   This is an immediate consequence of the fact that the centre entry satisfies
--   $3M_{1,1} = t$; see `MagicSquares.center_of_order_three`. Together with
--   `MagicSquares.magic_count_three_divisible` this determines $M_{3}$ completely.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707-717; arXiv:math/0201013v3, Section 2, MacMahon's formula for $M_{3}(t)$ (1915).

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem magic_count_three_otherwise (t : ℕ) (ht : ¬ 3 ∣ t) :
    magicCount 3 t = 0 := by sorry

end MagicSquares

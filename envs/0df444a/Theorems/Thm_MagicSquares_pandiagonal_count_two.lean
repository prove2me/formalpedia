-- Prove2me | Theorems.Thm_MagicSquares_pandiagonal_count_two
-- name    : MagicSquares.pandiagonal_count_two
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-18T15:36:57.428326+00:00
-- url     : https://prove2.me/theorems/f7c75790-c7d1-4eac-86f8-ea359a0db34f
-- title:
--   The pandiagonal squares of order two
-- statement:
--   **The order-two pandiagonal count.** With $P_{n}(t)$ the number of pandiagonal squares of order $n$ and line sum $t$ in the counting-theory sense of `IsPandiagonal` (semi-magic plus the wrapped diagonals parallel to the main diagonal), the theorem states
--
--   $$P_{2}(t)=\begin{cases}1,&2\mid t,\\ 0,&2\nmid t.\end{cases}$$
--
--   **Proof.** At order two the two wrapped diagonals of a semi-magic square are exactly its main and anti-diagonal, so `IsPandiagonal` coincides with `IsMagic` and $P_{2}=M_{2}$. This is the last order at which the two notions agree: from order three on they diverge.
-- source:
--   M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013).

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresPandiagonal
open MagicSquares

namespace MagicSquares

theorem pandiagonal_count_two (t : ℕ) : pandiagonalCount 2 t = if 2 ∣ t then 1 else 0 := by sorry

end MagicSquares

-- Prove2me | Theorems.Thm_MagicSquares_magic_count_two
-- name    : MagicSquares.magic_count_two
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-18T15:37:05.663889+00:00
-- url     : https://prove2.me/theorems/821e65d7-81bb-4802-9e30-cec0cb544afd
-- title:
--   The magic squares of order two
-- statement:
--   **The order-two magic count.** Writing $M_{n}(t)$ for the number of $n\times n$ arrays of nonnegative integers whose rows, columns and two main diagonals all sum to $t$, the theorem states
--
--   $$M_{2}(t)=\begin{cases}1,&2\mid t,\\ 0,&2\nmid t.\end{cases}$$
--
--   The single square is the constant array with every entry $t/2$. **Proof.** In the $\begin{pmatrix} a & t-a\\ t-a & a\end{pmatrix}$ family the two diagonals read $2a$ and $2(t-a)$; requiring both to equal $t$ forces $2a=t$. This is the first instance of the divisibility obstruction that governs every magic-square count: the diagonal conditions are not automatic, and they vanish off a sublattice of line sums.
-- source:
--   M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013).

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresPandiagonal
open MagicSquares

namespace MagicSquares

theorem magic_count_two (t : ℕ) : magicCount 2 t = if 2 ∣ t then 1 else 0 := by sorry

end MagicSquares

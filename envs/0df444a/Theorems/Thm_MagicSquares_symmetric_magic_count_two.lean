-- Prove2me | Theorems.Thm_MagicSquares_symmetric_magic_count_two
-- name    : MagicSquares.symmetric_magic_count_two
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-18T15:36:52.748885+00:00
-- url     : https://prove2.me/theorems/2f881f90-879c-41b8-a4d0-75a2b921c352
-- title:
--   The symmetric magic squares of order two
-- statement:
--   **The order-two symmetric count.** Writing $S_{n}(t)$ for the number of $n\times n$ arrays of nonnegative integers which are magic of line sum $t$ and equal to their own transpose, the theorem states
--
--   $$S_{2}(t)=\begin{cases}1,&2\mid t,\\ 0,&2\nmid t.\end{cases}$$
--
--   **Proof.** For order two the transpose condition is $M_{01}=M_{10}$, which already holds for every semi-magic square: the first row and first column both read $M_{00}+M_{01}=t$ and $M_{00}+M_{10}=t$. So symmetry adds no condition at order two, $S_{2}=M_{2}$, and the order-two magic count applies. Symmetry only starts to bite at order three, where it cuts the two-parameter MacMahon family down to a one-parameter one.
-- source:
--   M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013).

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresPandiagonal
open MagicSquares

namespace MagicSquares

theorem symmetric_magic_count_two (t : ℕ) : symmetricMagicCount 2 t = if 2 ∣ t then 1 else 0 := by sorry

end MagicSquares

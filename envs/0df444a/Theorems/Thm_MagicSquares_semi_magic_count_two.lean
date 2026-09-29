-- Prove2me | Theorems.Thm_MagicSquares_semi_magic_count_two
-- name    : MagicSquares.semi_magic_count_two
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-18T15:36:50.238006+00:00
-- url     : https://prove2.me/theorems/86515ed9-6bd4-4484-a3d2-a1be23ce7ac9
-- title:
--   The semi-magic squares of order two
-- statement:
--   **The order-two semi-magic count.** Writing $H_{n}(t)$ for the number of $n\times n$ arrays of nonnegative integers whose rows and columns all sum to $t$, the theorem states
--
--   $$H_{2}(t)=t+1 .$$
--
--   **Proof.** A $2\times2$ semi-magic square of line sum $t$ reads $\begin{pmatrix} a & t-a\\ t-a & a\end{pmatrix}$, so it is determined by its top-left corner $a$, and $a$ may be any of $0,1,\dots,t$. This is the first value in the structural statement that $H_{n}(t)$ is a polynomial of degree $(n-1)^{2}$ — for $n=2$ that is degree one, matching $t+1$.
-- source:
--   M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013).

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresPandiagonal
open MagicSquares

namespace MagicSquares

theorem semi_magic_count_two (t : ℕ) : semiMagicCount 2 t = t + 1 := by sorry

end MagicSquares

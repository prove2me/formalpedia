-- Prove2me | Theorems.Thm_MagicSquares_special_three_count
-- name    : MagicSquares.special_three_count
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-18T14:10:45.04373+00:00
-- url     : https://prove2.me/theorems/0e66e443-931d-419d-8ec0-b925b0678288
-- title:
--   The complete count of the special order-three magic squares
-- statement:
--   **The special classes of order-three magic squares, counted completely.**
--
--   Let $P_{3}(t)$ be the number of *panmagic* (pandiagonal) squares of order three
--   and line sum $t$ — those $3\times3$ arrays of nonnegative integers whose rows,
--   columns and all six broken diagonals sum to $t$ — and let $S_{3}(t)$ be the
--   number of *symmetric* magic squares of order three and line sum $t$. The theorem
--   determines both, for every $t$:
--
--   $$P_{3}(t)=\begin{cases}1,&3\mid t\\ 0,&3\nmid t\end{cases},
--   \qquad
--   S_{3}(t)=\begin{cases}\dfrac{2t}{3}+1,&3\mid t\\[2mm] 0,&3\nmid t\end{cases}.$$
--
--   **What the answers say.** Where MacMahon's count for the plain magic squares of
--   order three is quadratic ($M_{3}(3e)=2e^{2}+2e+1$), the two special classes are
--   degenerate in opposite ways. The six broken diagonals are so restrictive that
--   they collapse the whole two-parameter family to the single constant square: for
--   line sum $3e$ that is the array all of whose entries equal $e$. Symmetry, by
--   contrast, removes only three of the eight line conditions, and what survives is a
--   genuine one-parameter family
--
--   $$\begin{pmatrix} a & 2e-a & e\\ 2e-a & e & a\\ e & a & 2e-a\end{pmatrix},
--   \qquad a=0,1,\dots,2e ,$$
--
--   giving the linear count $2e+1$. In both cases the divisibility obstruction for
--   order-three magic squares — the centre equals one third of the line sum, by
--   `center_of_order_three` — forces the vanishing off multiples of three.
--
--   **Proof.** The two evaluations at $t=3e$ are supplied by `pan_three_card` and by
--   `symm_three_bij` composed with the cardinality of the parameter interval
--   $\{0,\dots,2e\}$; the two vanishing cases are supplied by
--   `pan_three_otherwise` and `symm_three_otherwise`, both of which reduce to the
--   centre identity. Splitting on whether $3\mid t$ and substituting $t=3e$ finishes
--   the count.
--
--   **Context.** This is the fourth and last instalment of the order-three programme:
--   after counting all squares (Mission I), all semi-magic ones (Mission II) and
--   classifying the normal ones (Mission III), the special classes complete the
--   picture. The comparison between the three counts — quadratic, linear and
--   constant — is the point of the order-three study, and it is what is lost at
--   order four, where no closed form is known.
-- source:
--   P. A. MacMahon, Combinatory Analysis, Vol. II, Cambridge University Press, 1916; M. Beck, T. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013); W. S. Andrews, Magic Squares and Cubes, 2nd ed., Dover, 1960.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresSpecial3
open MagicSquares

namespace MagicSquares

theorem special_three_count (t : ℕ) :
    panMagicCount 3 t = (if 3 ∣ t then 1 else 0) ∧
      symmetricMagicCount 3 t = (if 3 ∣ t then 2 * (t / 3) + 1 else 0) := by sorry

end MagicSquares

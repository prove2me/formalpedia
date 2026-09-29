-- Prove2me | Theorems.Thm_MagicSquares_pan_three_otherwise
-- name    : MagicSquares.pan_three_otherwise
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-18T14:10:30.305249+00:00
-- url     : https://prove2.me/theorems/025bcf4a-7b1e-4813-acfa-27f69cf2dcd5
-- title:
--   No panmagic squares of order three when the line sum is not divisible by three
-- statement:
--   **The zero case for panmagic squares.**
--
--   Writing $P_{n}(t)$ for the number of panmagic squares of order $n$ and line sum
--   $t$, the theorem is
--
--   $$3\nmid t\implies P_{3}(t)=0 .$$
--
--   It complements the evaluation $P_{3}(3e)=1$: together they give the complete
--   count $P_{3}(t)=1$ for $3\mid t$ and $P_{3}(t)=0$ otherwise.
--
--   **Proof.** A panmagic square is in particular a magic square, because the broken
--   diagonals of offset $0$ are exactly the two main diagonals. For a magic square of
--   order three and line sum $t$, the classical centre identity
--   `center_of_order_three` gives $3c=t$ where $c$ is the centre entry. Hence
--   $3\mid t$, and the square cannot exist when $t$ is not divisible by three.
--
--   **Context.** This is the standard divisibility obstruction for order-three magic
--   squares: the centre is forced to be one third of the line sum, so line sums
--   indivisible by three are impossible for any class that contains the magic
--   squares. The same argument already gave the vanishing of the plain magic count
--   `magic_count_three_otherwise` and of the semi-magic count; what the present
--   statement adds is only the observation that panmagicity is stronger than
--   magicity, so the obstruction is inherited.
-- source:
--   P. A. MacMahon, Combinatory Analysis, Vol. II, Cambridge University Press, 1916; M. Beck, T. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013); W. S. Andrews, Magic Squares and Cubes, 2nd ed., Dover, 1960.

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem pan_three_otherwise (t : ℕ) (ht : ¬ 3 ∣ t) : panMagicCount 3 t = 0 := by sorry

end MagicSquares

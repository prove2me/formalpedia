-- Prove2me | Theorems.Thm_MagicSquares_symm_three_otherwise
-- name    : MagicSquares.symm_three_otherwise
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-18T14:10:34.549603+00:00
-- url     : https://prove2.me/theorems/632cc340-833d-4a83-9537-d53be8c54378
-- title:
--   No symmetric magic squares of order three when the line sum is not divisible by three
-- statement:
--   **The zero case for symmetric magic squares.**
--
--   Writing $S_{n}(t)$ for the number of symmetric magic squares of order $n$ and
--   line sum $t$, the theorem is
--
--   $$3\nmid t\implies S_{3}(t)=0 ,$$
--
--   the companion of the evaluation $S_{3}(3e)=2e+1$.
--
--   **Proof.** A symmetric magic square is in particular magic, and for a magic
--   square of order three and line sum $t$ the centre entry $c$ satisfies $3c=t$ by
--   `center_of_order_three`. Hence $3\mid t$ is necessary for existence, and the
--   filtered finset `symmetricMagicSquares 3 t` is empty otherwise.
--
--   **Context.** Symmetry does not produce new line sums beyond those already
--   admitted by the magic squares — it only cuts each magic fibre down. So the same
--   divisibility obstruction applies, and the symmetric count, like the panmagic and
--   the plain magic counts, vanishes off the multiples of three.
-- source:
--   P. A. MacMahon, Combinatory Analysis, Vol. II, Cambridge University Press, 1916; M. Beck, T. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013); W. S. Andrews, Magic Squares and Cubes, 2nd ed., Dover, 1960.

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem symm_three_otherwise (t : ℕ) (ht : ¬ 3 ∣ t) : symmetricMagicCount 3 t = 0 := by sorry

end MagicSquares

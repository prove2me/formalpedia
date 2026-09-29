-- Prove2me | Theorems.Thm_MagicSquares_panmagic_count_three
-- name    : MagicSquares.panmagic_count_three
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-18T15:37:11.352748+00:00
-- url     : https://prove2.me/theorems/adc01be4-ceea-44d9-a371-80b76abda23a
-- title:
--   The two-direction panmagic squares of order three
-- statement:
--   **The order-three two-direction panmagic count.** This statement is about the stronger predicate `IsPanMagic`, which requires *both* families of broken diagonals (descending and ascending) to sum to the line sum, and it determines
--
--   $$P^{\mathrm{both}}_{3}(t)=\begin{cases}1,&3\mid t,\\ 0,&3\nmid t.\end{cases}$$
--
--   The single square at line sum $3e$ is the constant array with every entry $e$. **Context.** The purpose of this node is to sit next to `pandiagonal_count_three` so that the two readings of "pandiagonal" are both present on the platform and cannot be confused: the one-direction reading used by the counting literature gives a degree-two polynomial that never vanishes, whereas the two-direction reading collapses to the constant square and vanishes off multiples of three. Citing one in place of the other is the most likely faithfulness error in this area.
-- source:
--   M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013).

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresPandiagonal
open MagicSquares

namespace MagicSquares

theorem panmagic_count_three (t : ℕ) : panMagicCount 3 t = if 3 ∣ t then 1 else 0 := by sorry

end MagicSquares

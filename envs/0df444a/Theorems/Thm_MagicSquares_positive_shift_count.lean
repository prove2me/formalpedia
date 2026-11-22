-- Prove2me | Theorems.Thm_MagicSquares_positive_shift_count
-- name    : MagicSquares.positive_shift_count
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-20T21:16:16.06684+00:00
-- url     : https://prove2.me/theorems/c193b4f1-946c-440d-ae6f-76fdf8a54d6f
-- title:
--   Positive semi-magic squares shift to line sum t - n
-- statement:
--   **The shift bijection between positive and ordinary semi-magic squares.** Let $n \ge 1$ and $t \ge n$. Subtracting the all-ones matrix $J$ gives a bijection between the positive semi-magic squares of line sum $t$ (every entry at least one) and all semi-magic squares of line sum $t - n$, so that$$I_{n}(t) = H_{n}(t - n).$$
--
--   The map is its own inverse up to adding $J$ back: since $J$ itself has every line sum equal to $n$, subtracting it drops every line sum by exactly $n$ while preserving nonnegativity precisely for the positive squares. This is the elementary combinatorial half of Stanley's reciprocity argument: it converts the geometric interior count supplied by Ehrhart--Macdonald reciprocity into an ordinary value of the counting function, with no polyhedral machinery of its own.
--
--   **Formalization Note** Lean states both sides as cardinals over `Square n (Fin (t+1))`-style finsets via `positiveInteriorCount` and `semiMagicCount`, with `t - n` the truncated natural subtraction (exact here since $t \ge n$).
-- source:
--   R. P. Stanley, Duke Math. J. 40 (1973), 607--632, interior points of dilates of the Birkhoff polytope via the all-ones shift; M. Beck and D. Paxton, The Ehrhart polynomial of the Birkhoff polytope (arXiv:math.CO/0202267).

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquares_positiveInteriorCount
open MagicSquares

namespace MagicSquares

theorem positive_shift_count (n t : ℕ) (hn : 1 ≤ n) (hnt : n ≤ t) :
    positiveInteriorCount n t = semiMagicCount n (t - n) := by sorry

end MagicSquares

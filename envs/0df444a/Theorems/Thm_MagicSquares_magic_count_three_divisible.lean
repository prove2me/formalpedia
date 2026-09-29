-- Prove2me | Theorems.Thm_MagicSquares_magic_count_three_divisible
-- name    : MagicSquares.magic_count_three_divisible
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T12:11:47.284419+00:00
-- url     : https://prove2.me/theorems/393a2adc-5e8e-4847-b9c6-f7b141a5114e
-- title:
--   MacMahon's count of 3x3 magic squares with line sum a multiple of 3
-- statement:
--   MacMahon's 1915 count of $3 \times 3$ magic squares
--   whose line sum is a multiple of $3$.
--
--   Write $M_{3}(t)$ for the number of $3 \times 3$ arrays of nonnegative integers whose three
--   rows, three columns and two main diagonals all sum to $t$ (entries need not be distinct). Then
--   $M_{3}(t)$ vanishes unless $3 \mid t$, and for $t = 3e$,
--
--   $$
--   M_{3}(3e) = 2e^{2} + 2e + 1 ,
--   $$
--
--   which is the integral form of $\tfrac{2}{9}t^{2} + \tfrac{2}{3}t + 1$.
--
--   The companion statement `MagicSquares.magic_count_three_otherwise` records the vanishing when
--   $3 \nmid t$; together they give the complete counting function.
--
--   **Formalization Note** `magicCount n t` counts arrays with entries in `Fin (t+1)` satisfying
--   the magic identities after coercion to `ℕ`. This is lossless because every entry of a
--   nonnegative magic square with line sum $t$ is at most $t$.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707-717; arXiv:math/0201013v3, Section 2, MacMahon's formula for $M_{3}(t)$ (1915).

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem magic_count_three_divisible (e : ℕ) :
    magicCount 3 (3 * e) = 2 * e ^ 2 + 2 * e + 1 := by sorry

end MagicSquares

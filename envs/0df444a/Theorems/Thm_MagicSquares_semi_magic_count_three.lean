-- Prove2me | Theorems.Thm_MagicSquares_semi_magic_count_three
-- name    : MagicSquares.semi_magic_count_three
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T12:11:48.971843+00:00
-- url     : https://prove2.me/theorems/55e2191d-be25-4e6d-af7a-4635a34e5c63
-- title:
--   MacMahon's count of 3x3 semi-magic squares by line sum
-- statement:
--   MacMahon's 1915 formula for the number of
--   $3 \times 3$ semi-magic squares of a given line sum.
--
--   Write $H_{3}(t)$ for the number of $3 \times 3$ arrays of nonnegative integers whose three rows
--   and three columns all sum to $t$ (the diagonals are unconstrained, and entries need not be
--   distinct). Then
--
--   $$
--   H_{3}(t) = 3\binom{t+3}{4} + \binom{t+2}{2}.
--   $$
--
--   Unlike the magic count $M_{3}(t)$, this is an honest polynomial in $t$ of degree
--   $(3-1)^{2} = 4$: Ehrhart and Stanley proved that $H_{n}(t)$ is a polynomial of degree
--   $(n-1)^{2}$ for every $n$, satisfying the reciprocity law $H_{n}(-n-t) = (-1)^{n-1}H_{n}(t)$.
--
--   **Formalization Note** `semiMagicCount n t` counts arrays with entries in `Fin (t+1)` whose
--   row and column sums are $t$ after coercion to `ℕ`; the bound on entries makes the finite
--   search space exact.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707-717; arXiv:math/0201013v3, Section 2, Theorem 1 (MacMahon's formula for $H_{3}(t)$).

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem semi_magic_count_three (t : ℕ) :
    semiMagicCount 3 t = 3 * ((t + 3).choose 4) + ((t + 2).choose 2) := by sorry

end MagicSquares

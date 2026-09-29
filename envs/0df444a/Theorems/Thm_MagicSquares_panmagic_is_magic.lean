-- Prove2me | Theorems.Thm_MagicSquares_panmagic_is_magic
-- name    : MagicSquares.panmagic_is_magic
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T13:52:13.866903+00:00
-- url     : https://prove2.me/theorems/1ece0a73-2e26-4db4-9f45-5d2d39f1d53d
-- title:
--   Every panmagic square is magic
-- statement:
--   A **panmagic** (pandiagonal) square is in particular a magic square.
--
--   By definition `IsPanMagic M s` requires every row and every column to sum to $s$
--   (the semi-magic condition) and, in addition, *every* broken diagonal in both
--   directions to sum to $s$. The two main diagonals are the broken diagonals of
--   offset $0$, so both main diagonal sums equal $s$, which is exactly the extra
--   content of `IsMagic M s` over `IsSemiMagic M s`.
--
--   **Formalization Note** `brokenDiagSum M k` is $\sum_i M_{i,\, i+k}$ with the column
--   index read modulo $n$, so `brokenDiagSum M 0 = diagSum M`. For the anti-diagonal one
--   uses `brokenAntiDiagSum M 0`, i.e. $\sum_i M_{i,\, n-1-i}$, which is
--   `antiDiagSum M`. Only $n \neq 0$ is needed so that `Fin n` carries the additive
--   structure used to speak of offsets.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717; arXiv:math/0201013v3., Section 1 (definitions of $P_n$ versus $M_n$).

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem panmagic_is_magic {n : ℕ} [NeZero n]
    (M : Square n ℕ) (s : ℕ) (hP : IsPanMagic M s) :
    IsMagic M s := by sorry

end MagicSquares

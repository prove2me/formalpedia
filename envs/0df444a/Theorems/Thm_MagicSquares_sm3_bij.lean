-- Prove2me | Theorems.Thm_MagicSquares_sm3_bij
-- name    : MagicSquares.sm3_bij
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T18:23:38.571607+00:00
-- url     : https://prove2.me/theorems/c4897555-460d-4fc5-8a01-732b5d8f39c9
-- title:
--   Bijection between semi-magic squares and normalized parameters
-- statement:
--   The map
--
--   $$(u,v,w,x,y,z)\longmapsto uD+vE+wF+xA+yB+zC$$
--
--   is a bijection from the normalized coefficient vectors — six nonnegative
--   integers summing to $t$ with $\min(x,y,z)=0$ — onto the $3\times3$ semi-magic
--   squares of line sum $t$. Consequently
--
--   $$H_{3}(t)=\mathrm{sm3Count}(t).$$
--
--   Surjectivity and injectivity are exactly the two halves of `sm3_canonical`;
--   what is left is the bookkeeping that turns a bijection of carriers into an
--   equality of `Finset.card`s. Two coercions have to be handled explicitly. First,
--   `semiMagicCount 3 t` counts arrays with entries in `Fin (t+1)`, so the forward
--   map must be read into that finite type — legitimate because every entry of a
--   semi-magic square of line sum $t$ is at most $t$. Second, `sm3Count t` counts
--   functions `Fin 6 → Fin (t+1)`, and the bound is again lossless because the six
--   coefficients sum to $t$.
--
--   **Formalization Note** Both directions therefore need a `Finset.card_bij`
--   with an explicit proof that the round trip is the identity on each side.
-- source:
--   P. A. MacMahon, Combinatory Analysis (1915); M. Beck, T. Cohen, J. Cuomo, P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707-717; arXiv:math/0201013v3, Section 2, Theorem 1.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresSemiMagic3
open MagicSquares

namespace MagicSquares

theorem sm3_bij (t : ℕ) : semiMagicCount 3 t = sm3Count t := by sorry

end MagicSquares

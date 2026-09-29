-- Prove2me | Theorems.Thm_MagicSquares_magic_three_param_bij
-- name    : MagicSquares.magic_three_param_bij
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T14:14:58.356034+00:00
-- url     : https://prove2.me/theorems/f62c9364-c183-42f8-84b8-a6ac8e72ade7
-- title:
--   MacMahon parametrization: 3x3 magic squares vs admissible pairs
-- statement:
--   The map
--   $$M \longmapsto (M_{00},\, M_{02})$$
--   is a bijection from the $3 \times 3$ magic squares with nonnegative entries and
--   line sum $3e$ onto the admissible parameter pairs
--   $$\{(a,c) \in \mathbb{N}^{2} : e \le a + c \le 3e,\; a \le e + c,\; c \le e + a\}.$$
--   Consequently the two counting functions agree: $M_{3}(3e) = \mathrm{paramCount}(e)$.
--
--   **Injectivity.** MacMahon's centre identity gives $M_{11} = e$; then the diagonal
--   and anti-diagonal identities give $M_{22} = 2e - a$ and $M_{20} = 2e - c$, the row
--   and column identities fill in $M_{01} = 3e - a - c$, $M_{21} = a + c - e$,
--   $M_{10} = e + c - a$, $M_{12} = e + a - c$, and $M_{02} = c$, $M_{00} = a$ by
--   definition. So $(a,c)$ determines $M$ completely.
--
--   **Surjectivity.** Given an admissible pair, the array `mkMagic3 e a c` has
--   nonnegative entries (that is exactly what admissibility says, together with the
--   implied bounds $a, c \le 2e$) and its three rows, three columns and two diagonals
--   all sum to $3e$; each entry is at most $3e$, so it lies in the search space
--   $\{0,\dots,3e\}$ used by `magicCount`.
--
--   **Formalization Note** `magicCount 3 (3*e)` counts arrays with entries in
--   `Fin (3*e+1)`; `paramCount e` counts the finset `paramSet e`. The bijection is
--   expressed as an equality of cardinalities.
-- source:
--   P. A. MacMahon, Combinatory Analysis (1915); G. Xin, Constructing all magic squares of order three (2008).

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3
open MagicSquares

namespace MagicSquares

theorem magic_three_param_bij (e : ℕ) :
    magicCount 3 (3 * e) = paramCount e := by sorry

end MagicSquares

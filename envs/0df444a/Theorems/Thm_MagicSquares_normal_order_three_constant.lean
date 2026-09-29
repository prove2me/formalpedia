-- Prove2me | Theorems.Thm_MagicSquares_normal_order_three_constant
-- name    : MagicSquares.normal_order_three_constant
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T13:52:09.498225+00:00
-- url     : https://prove2.me/theorems/08463353-63d3-4260-89cf-9f61e97f7a04
-- title:
--   The magic constant of a normal 3x3 magic square is 15
-- statement:
--   Every normal $3 \times 3$ magic square has line sum $15$.
--
--   A **normal** magic square of order $3$ has entries exactly $1, 2, \dots, 9$, each used once.
--   Its magic constant is therefore
--   $$\frac{1}{3}\,(1 + 2 + \cdots + 9) = \frac{45}{3} = 15 .$$
--
--   This is the $n = 3$ instance of the general magic-constant identity
--   $2s = n(n^{2}+1)$, which here reads $2s = 3 \cdot 10 = 30$.
--
--   **Formalization Note** The statement avoids division: with the hypothesis
--   `IsNormal M` and `IsMagic M s` the general identity gives `2 * s = 30`, and `s = 15`
--   follows by linear arithmetic over $\mathbb{N}$.
-- source:
--   Standard folklore on the Lo Shu square; the general identity is the magic-constant formula for normal magic squares.

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem normal_order_three_constant (M : Square 3 ℕ) (s : ℕ)
    (hN : IsNormal M) (hM : IsMagic M s) :
    s = 15 := by sorry

end MagicSquares

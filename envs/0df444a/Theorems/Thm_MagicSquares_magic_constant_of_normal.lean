-- Prove2me | Theorems.Thm_MagicSquares_magic_constant_of_normal
-- name    : MagicSquares.magic_constant_of_normal
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T12:11:46.019893+00:00
-- url     : https://prove2.me/theorems/2b184629-25ee-4be3-9075-89d9e624208d
-- title:
--   Magic constant of a normal magic square
-- statement:
--   Every normal magic square has the magic constant
--   $n(n^{2}+1)/2$.
--
--   Let $M$ be an $n \times n$ array whose entries are exactly the integers $1,2,\dots,n^{2}$,
--   each used once, and suppose every row, every column and both main diagonals of $M$ sum to the
--   same number $s$. Then
--
--   $$
--   2s = n\,(n^{2}+1).
--   $$
--
--   Equivalently $s = n(n^{2}+1)/2$, the classical magic constant: it is $\tfrac{1}{n}$ of the sum
--   $1+2+\cdots+n^{2} = n^{2}(n^{2}+1)/2$ of all entries.
--
--   **Formalization Note** The division by $2$ is avoided by multiplying through, so the statement
--   is an identity in $\mathbb{N}$. Normality is the conjunction of the entry bounds
--   $1 \le M_{ij} \le n^{2}$ with injectivity of the index-to-entry map.
-- source:
--   Standard folklore; stated e.g. in Weisstein, MathWorld, "Magic Square", eq. for the magic constant of a normal magic square.

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem magic_constant_of_normal (n : ℕ) (M : Square n ℕ) (s : ℕ)
    (hN : IsNormal M) (hM : IsMagic M s) :
    2 * s = n * (n ^ 2 + 1) := by sorry

end MagicSquares

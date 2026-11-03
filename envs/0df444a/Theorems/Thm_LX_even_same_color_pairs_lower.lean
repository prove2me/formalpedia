-- Prove2me | Theorems.Thm_LX_even_same_color_pairs_lower
-- name    : LX.even_same_color_pairs_lower
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:00:44.725276+00:00
-- url     : https://prove2.me/theorems/fb63b809-7eba-420d-a244-79d4a8687074
-- title:
--   A two-coloring of twice m positions has at least m times m minus one same-color pairs
-- statement:
--   Let $n,m$ be natural numbers with $n=2m$, and color the positions $0,\ldots,n-1$ with two colors. Let $M(\chi)$ count unordered pairs of distinct positions having the same color, counted once by taking indices $i<j$. Then
--
--   $$
--   M(\chi)\ge m(m-1).
--   $$
--
--   There is no nonemptiness assumption: the case $m=0$ gives the empty coloring and the case $m=1$ gives a zero lower bound. Balanced color classes attain the bound. In the affine reflection argument, the two colors represent winding parity, so this elementary estimate supplies a uniform number of inversion-charged pairs.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/TwoColorPairs.lean#L60-L73

/-
Adapted from https://github.com/snow-ghost/glushkov-lx-lean at 8cddcd222b591673dc63475d9d45b9ed5c6eb92c.
MIT License

Copyright (c) 2026 S. Uskov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Mathlib
import Definitions.Def_LX_TwoColorPairs

namespace LX
end LX

namespace LX
end LX
open LX
open scoped BigOperators
variable {n : ℕ}

theorem LX.even_same_color_pairs_lower (χ : Fin n → Bool) (m : ℕ) (hn : n=2*m) :
    m*(m-1) ≤ sameColorPairs χ := by sorry

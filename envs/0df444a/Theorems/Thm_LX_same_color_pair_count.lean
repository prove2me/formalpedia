-- Prove2me | Theorems.Thm_LX_same_color_pair_count
-- name    : LX.same_color_pair_count
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:00:43.771952+00:00
-- url     : https://prove2.me/theorems/6a6e0c23-62d6-4436-b0ba-8806f6291866
-- title:
--   The same-color pair count is determined by the squared color-class sizes
-- statement:
--   Let $n$ be a natural number and let $\chi:\{0,\ldots,n-1\}\to\{0,1\}$ be any two-coloring. Write $c_0,c_1$ for the sizes of its two color classes and let $M(\chi)$ count pairs $i<j$ with $\chi(i)=\chi(j)$. Then
--
--   $$
--   2M(\chi)+n=c_0^2+c_1^2.
--   $$
--
--   The diagonal contributes exactly $n$, including when one color class is empty; each distinct same-color pair contributes twice to the squared class counts. This identity converts pair counting into a quadratic expression in class sizes, enabling lower bounds by balancing the two classes.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/TwoColorPairs.lean#L21-L58

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

theorem LX.same_color_pair_count (χ : Fin n → Bool) :
    2*sameColorPairs χ+n=(colorCount χ true)^2+(colorCount χ false)^2 := by sorry

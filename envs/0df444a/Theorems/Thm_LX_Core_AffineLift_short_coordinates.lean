-- Prove2me | Theorems.Thm_LX_Core_AffineLift_short_coordinates
-- name    : LX.Core.AffineLift.short_coordinates
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:35.797249+00:00
-- url     : https://prove2.me/theorems/01e272c5-e178-4212-b0cc-b9cd6ee6df4d
-- title:
--   Short coordinates from subset majorization
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. A board is majorized if $2\sum_{i\in S}d_i\le |S|(n-|S|)$ for every subset $S\subseteq I_n$. Let $n\in\mathbb N$ and $d:I_n\to\mathbb Z$ satisfy $\sum_i d_i=0$ and be majorized. Every coordinate satisfies
--
--   $$
--   -(n-1)\le2d_i\le n-1\qquad(i\in I_n).
--   $$
--
--   The doubled integer form retains the parity slack in the half-circle bound. For $n=0$, the coordinate assertion is vacuous.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AffineLift.lean#L106-L123

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
import Definitions.Def_LX_AffineLift

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace List
end List

namespace LX.Core.AffineLift
end LX.Core.AffineLift
open LX
open LX.Core
open LX.Core.AffineLift
open scoped BigOperators

theorem LX.Core.AffineLift.short_coordinates {n : ℕ} {d : Fin n → ℤ}
    (hd : ∑ i, d i = 0) (hm : Majorized d) (i : Fin n) :
    2 * d i ≤ (n : ℤ) - 1 ∧ -((n : ℤ) - 1) ≤ 2 * d i := by sorry

-- Prove2me | Theorems.Thm_LX_Core_AffineLift_crossing_unit
-- name    : LX.Core.AffineLift.crossing_unit
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:38.274359+00:00
-- url     : https://prove2.me/theorems/8b9822ce-5943-4b5a-bfb6-e0142240aade
-- title:
--   Unit crossings in a majorized board
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For an integer board $d:I_n\to\mathbb Z$, put $F_i=i+d_i$, $\lambda_i=F_i\bmod n$, $C_{ij}=-\lfloor(((j-i)\bmod n)+d_j-d_i)/n\rfloor$, $B_i=\sum_j\max(-C_{ij},0)$, and $I(d)=\sum_{i<j}|\lfloor(F_j-F_i)/n\rfloor|$. A board is majorized if $2\sum_{i\in S}d_i\le |S|(n-|S|)$ for every subset $S\subseteq I_n$. Assume $n>0$, $\sum_i d_i=0$, and $d$ is majorized. Then
--
--   $$
--   |C_{ij}|\le1\qquad(i,j\in I_n).
--   $$
--
--   Majorization limits every signed pair interaction to one crossing in either direction.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AffineCrossings.lean#L116-L133

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
import Definitions.Def_LX_AffineCrossings
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
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.Core.AffineLift.crossing_unit {d : Fin n → ℤ} (hd : ∑ i, d i = 0)
    (hm : Majorized d) (i j : Fin n) : |crossing d i j| ≤ 1 := by sorry

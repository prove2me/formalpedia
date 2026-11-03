-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_exists_zero_gap
-- name    : LX.Core.ZeroGap.exists_zero_gap
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:59:12.198463+00:00
-- url     : https://prove2.me/theorems/57092591-3b2c-4df6-b467-b05a0492327f
-- title:
--   A balanced nonzero cyclic vector has a positive-to-negative gap with zero interior
-- statement:
--   Let $n>0$ and let $d:\mathbb Z/n\mathbb Z\to\mathbb Z$ have total sum zero and at least one nonzero coordinate. Define clockwise distance by $\delta(u,v)=\operatorname{rep}(v-u)$, where the representative lies in $\{0,\ldots,n-1\}$. There exist positions $u,v$ such that
--
--   $$
--   d(u)>0,\quad d(v)<0,\quad\delta(u,v)>0,
--   \qquad
--   0<\delta(u,j)<\delta(u,v)\ \Longrightarrow\ d(j)=0.
--   $$
--
--   Thus some positive coordinate is followed by a negative coordinate with only zero coordinates on the intervening clockwise arc. This supplies the zero-gap endpoints used to make a sorting descent.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapPair.lean#L33-L58

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
import Definitions.Def_LX_ZeroGapPair

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.Core.ZeroGap.exists_zero_gap (d : Fin n → ℤ) (hd : ∑ i, d i=0) (hne : ∃ i, d i ≠ 0) :
    ∃ u v : Fin n, 0 < d u ∧ d v < 0 ∧ 0 < distance u v ∧
      ∀ j, 0 < distance u j → distance u j < distance u v → d j=0 := by sorry

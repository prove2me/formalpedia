-- Prove2me | Theorems.Thm_LX_AffineScan_join_minima_majorized
-- name    : LX.AffineScan.join_minima_majorized
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:23:45.432377+00:00
-- url     : https://prove2.me/theorems/ce060588-db85-4e9e-b095-5ac3d9b8ec4d
-- title:
--   Joining two negative-extreme coordinates preserves majorization
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. A board is majorized if $2\sum_{i\in S}d_i\le |S|(n-|S|)$ for every subset $S\subseteq I_n$. For distinct $u,v\in I_n$, define $J_{u,v}(d)_i=d_i-1+\mathbf1_{i=u}+(n-1)\mathbf1_{i=v}$. Let $n>0$, let $d$ be balanced and majorized, and let $n=2h+3$ for $h\in\mathbb N$. Assume $u\ne v$ and $d_u=d_v=-h$. Then
--
--   $$
--   J_{u,v}(d)\text{ is majorized}.
--   $$
--
--   The special odd-size relation makes the joined-board subset inequalities valid.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/JoinMinimumPair.lean#L24-L77

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
import Definitions.Def_LX_JoinMinimumPair

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace List
end List

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AffineScan.join_minima_majorized (d : Fin n → ℤ) (u v : Fin n) (hne : u ≠ v)
    (hb : ∑ i,d i=0) (hm : Majorized d) (h : ℕ) (hn : n=2*h+3)
    (hu : d u= -(h : ℤ)) (hv : d v= -(h : ℤ)) :
    Majorized (joinMinima d u v) := by sorry

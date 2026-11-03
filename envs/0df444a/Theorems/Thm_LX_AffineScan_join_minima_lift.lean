-- Prove2me | Theorems.Thm_LX_AffineScan_join_minima_lift
-- name    : LX.AffineScan.join_minima_lift
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:23:39.485657+00:00
-- url     : https://prove2.me/theorems/c2d59fbd-b2a5-4f29-896b-81edf47b8d61
-- title:
--   Joining equal adjacent coordinates gives a shifted lift
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. A balanced lift of a permutation $p$ with phase $c$ means $\sum_i d_i=0$ and $i+d_i\equiv p^{-1}(i)+c\pmod n$. For distinct $u,v\in I_n$, define $J_{u,v}(d)_i=d_i-1+\mathbf1_{i=u}+(n-1)\mathbf1_{i=v}$. Let $n>0$, let $d$ lift $p^{-1}$ at integer phase $c$, and assume $v=u+1$ modulo $n$ and $d_u=d_v$. Then
--
--   $$
--   J_{u,v}(d)\text{ lifts }(p\circ(u\ v))^{-1}\text{ at phase }c-1.
--   $$
--
--   The joined board incorporates an adjacent permutation exchange and shifts the physical phase by one.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/JoinMinimumPair.lean#L86-L116

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
import Definitions.Def_LX_WordMetric

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

theorem LX.AffineScan.join_minima_lift {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p.symm c d) (u v : Fin n) (hne : u ≠ v)
    (hv : v=u+1) (he : d u=d v) :
    IsLift (p*Equiv.swap u v).symm (c-1) (joinMinima d u v) := by sorry

-- Prove2me | Theorems.Thm_LX_AffineScan_rotate_threshold_rank
-- name    : LX.AffineScan.rotate_threshold_rank
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:58:17.253228+00:00
-- url     : https://prove2.me/theorems/1861e5c8-529e-4819-a231-9e12bdfc707c
-- title:
--   Transporting threshold rank under rotation
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For an integer board $d:I_n\to\mathbb Z$, put $F_i=i+d_i$, $\lambda_i=F_i\bmod n$, $C_{ij}=-\lfloor(((j-i)\bmod n)+d_j-d_i)/n\rfloor$, $B_i=\sum_j\max(-C_{ij},0)$, and $I(d)=\sum_{i<j}|\lfloor(F_j-F_i)/n\rfloor|$. Define the threshold rank $R_d(r,v)=\sum_j\max(\lfloor(F_j-v)/n\rfloor+\mathbf1_{j\le r},0)$ and $T_d(v)=\sum_{j\ne0,1}\max(\lfloor(F_j-v)/n\rfloor,0)$. For $n\ge2$, set $A(d)_i=d_{i+1}$, using cyclic indices. For $r\in I_n$ and $v\in\mathbb Z$,
--
--   $$
--   R_{A(d)}(r,v)=R_d(r+1,v+1-n\mathbf1_{r=n-1}).
--   $$
--
--   The seam correction transports integer thresholds consistently around the circle.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AffineRankRotation.lean#L8-L57

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
import Definitions.Def_LX_AffineRankOrder
import Definitions.Def_LX_AffineScan

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
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace List
end List

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.AffineScan.rotate_threshold_rank (hn : 2 ≤ n) (d : Fin n → ℤ) (r : Fin n) (v : ℤ) :
    thresholdRank (rotate d) r v=
      thresholdRank d (finRotate n r)
        (v+1-(if r.val=n-1 then (1 : ℤ) else 0)*n) := by sorry

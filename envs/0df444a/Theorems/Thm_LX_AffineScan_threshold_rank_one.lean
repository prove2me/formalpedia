-- Prove2me | Theorems.Thm_LX_AffineScan_threshold_rank_one
-- name    : LX.AffineScan.threshold_rank_one
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:41.531266+00:00
-- url     : https://prove2.me/theorems/5475a3d4-c980-4f41-b203-a0e37d8a2439
-- title:
--   Threshold rank at position 1
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For an integer board $d:I_n\to\mathbb Z$, put $F_i=i+d_i$, $\lambda_i=F_i\bmod n$, $C_{ij}=-\lfloor(((j-i)\bmod n)+d_j-d_i)/n\rfloor$, $B_i=\sum_j\max(-C_{ij},0)$, and $I(d)=\sum_{i<j}|\lfloor(F_j-F_i)/n\rfloor|$. Define the threshold rank $R_d(r,v)=\sum_j\max(\lfloor(F_j-v)/n\rfloor+\mathbf1_{j\le r},0)$ and $T_d(v)=\sum_{j\ne0,1}\max(\lfloor(F_j-v)/n\rfloor,0)$. For $n\ge2$, any integer board $d$, and any threshold $v\in\mathbb Z$,
--
--   $$
--   R_d(1,v)=T_d(v)+\max(\lfloor(F_0-v)/n\rfloor+1,0)+\max(\lfloor(F_1-v)/n\rfloor+1,0).
--   $$
--
--   This separates the two head contributions from the common tail in a local comparison.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AffineRankOrder.lean#L47-L65

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
import Definitions.Def_LX_ScanInversions

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

theorem LX.AffineScan.threshold_rank_one (hn : 2 ≤ n) (d : Fin n → ℤ) (v : ℤ) :
    thresholdRank d 1 v=_root_.LX.UploadDefinitions.AffineRankOrder.rankTail d v+
      max ((targets d 0-v)/(n : ℤ)+1) 0+max ((targets d 1-v)/(n : ℤ)+1) 0 := by sorry

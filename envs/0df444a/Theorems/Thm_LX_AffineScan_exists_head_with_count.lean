-- Prove2me | Theorems.Thm_LX_AffineScan_exists_head_with_count
-- name    : LX.AffineScan.exists_head_with_count
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:11:21.899267+00:00
-- url     : https://prove2.me/theorems/6c7c608d-f4ac-450d-a5d5-ee4cac6fce94
-- title:
--   A nonmaximal head occurs early relative to the top count
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For an integer board $d:I_n\to\mathbb Z$, put $F_i=i+d_i$, $\lambda_i=F_i\bmod n$, $C_{ij}=-\lfloor(((j-i)\bmod n)+d_j-d_i)/n\rfloor$, $B_i=\sum_j\max(-C_{ij},0)$, and $I(d)=\sum_{i<j}|\lfloor(F_j-F_i)/n\rfloor|$. Write $K_d(k)=|\{i:B_i\ge k\}|$. Let $Q$ compare the head targets into increasing order, let $U(d)=A(Q(d))$ be one comparison followed by rotation, and let $U^t$ denote $t$ sweeps. Let $n>0$ and $h\in\mathbb N$ with $h>0$. Then
--
--   $$
--   \exists r\in I_n:\quad r\le K_d(h),\quad B_r<h.
--   $$
--
--   The first token below a depth threshold lies no later than the number at or above that threshold.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ExchangeReserve.lean#L10-L33

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
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_DepthCrowding

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteGaps
end LX.Core.FiniteGaps
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace List
end List

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AffineScan.exists_head_with_count (d : Fin n → ℤ) (h : ℕ) (hh : 0 < h) :
    ∃ r : Fin n,r.val ≤ depthCount d h ∧ backwardDepth d r < h := by sorry

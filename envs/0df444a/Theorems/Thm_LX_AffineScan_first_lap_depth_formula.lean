-- Prove2me | Theorems.Thm_LX_AffineScan_first_lap_depth_formula
-- name    : LX.AffineScan.first_lap_depth_formula
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:06:20.603953+00:00
-- url     : https://prove2.me/theorems/e7c34ac1-c51c-46ce-b575-081d98cccf89
-- title:
--   Depth profile after the first lap
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For an integer board $d:I_n\to\mathbb Z$, put $F_i=i+d_i$, $\lambda_i=F_i\bmod n$, $C_{ij}=-\lfloor(((j-i)\bmod n)+d_j-d_i)/n\rfloor$, $B_i=\sum_j\max(-C_{ij},0)$, and $I(d)=\sum_{i<j}|\lfloor(F_j-F_i)/n\rfloor|$. Write $K_d(k)=|\{i:B_i\ge k\}|$. Let $Q$ compare the head targets into increasing order, let $U(d)=A(Q(d))$ be one comparison followed by rotation, and let $U^t$ denote $t$ sweeps. For $1\le j<n$, define $e_j=B_j-1$ if some earlier target exceeds $F_j$, and otherwise $e_j=\min_{0\le t<j}B_t$; the subtraction is truncated in $\mathbb N$. Let $n\ge2$ and assume distinct residue labels. Then
--
--   $$
--   B_{U^{n-1}(d)}(i)=\begin{cases}0,&i=0,\\e_i,&i\ne0.\end{cases}
--   $$
--
--   The full first-lap queue is explicit in terms of original targets and depths.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FirstLapFormula.lean#L98-L115

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
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_FirstLapFormula
import Definitions.Def_LX_SweepCarrier

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

theorem LX.AffineScan.first_lap_depth_formula (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (i : Fin n) :
    backwardDepth (sweep d (n-1)) i = if i=0 then 0 else emittedDepth d i.val := by sorry

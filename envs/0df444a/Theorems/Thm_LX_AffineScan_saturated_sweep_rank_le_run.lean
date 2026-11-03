-- Prove2me | Theorems.Thm_LX_AffineScan_saturated_sweep_rank_le_run
-- name    : LX.AffineScan.saturated_sweep_rank_le_run
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:01:48.302311+00:00
-- url     : https://prove2.me/theorems/f7c17021-4714-4e54-87ce-99b48cd08172
-- title:
--   Saturated greedy sweeps dominate every schedule in rank order
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For an integer board $d:I_n\to\mathbb Z$, put $F_i=i+d_i$, $\lambda_i=F_i\bmod n$, $C_{ij}=-\lfloor(((j-i)\bmod n)+d_j-d_i)/n\rfloor$, $B_i=\sum_j\max(-C_{ij},0)$, and $I(d)=\sum_{i<j}|\lfloor(F_j-F_i)/n\rfloor|$. Define the threshold rank $R_d(r,v)=\sum_j\max(\lfloor(F_j-v)/n\rfloor+\mathbf1_{j\le r},0)$ and $T_d(v)=\sum_{j\ne0,1}\max(\lfloor(F_j-v)/n\rfloor,0)$. Let $E(d)_0=d_1+1$, $E(d)_1=d_0-1$, and $E(d)_i=d_i$ otherwise; let $Q(d)$ equal $E(d)$ when $d_1+1<d_0$ and equal $d$ otherwise. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. For $n\ge2$, define $V_t(d)=Q(U^t(d))$, so comparison occurs before and after every cursor advance. For any word $w$,
--
--   $$
--   R_{V_{\#_L(w)}(d)}(r,v)\le R_{\operatorname{run}(w,d)}(r,v)\qquad(r\in I_n,\ v\in\mathbb Z).
--   $$
--
--   At a fixed number of forward rotations, saturated comparison gives a universal rank improvement.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/GreedyRotationOptimality.lean#L30-L47

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
import Definitions.Def_LX_GreedyRotationOptimality
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

theorem LX.AffineScan.saturated_sweep_rank_le_run (hn : 2 ≤ n) (d : Fin n → ℤ) (w : List Letter) :
    RankLE (saturatedSweep d (w.count .l)) (run w d) := by sorry

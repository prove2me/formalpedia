-- Prove2me | Theorems.Thm_LX_LiftedScan_delete_adjacent_descent
-- name    : LX.LiftedScan.delete_adjacent_descent
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:09.054319+00:00
-- url     : https://prove2.me/theorems/954dc54d-a62d-4a3f-b58b-97ec216449bf
-- title:
--   Deleting an adjacent descending pair
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For an integer board $d:I_n\to\mathbb Z$, put $F_i=i+d_i$, $\lambda_i=F_i\bmod n$, $C_{ij}=-\lfloor(((j-i)\bmod n)+d_j-d_i)/n\rfloor$, $B_i=\sum_j\max(-C_{ij},0)$, and $I(d)=\sum_{i<j}|\lfloor(F_j-F_i)/n\rfloor|$. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. Assume $n\ge2$, $p\operatorname{ev}(w)=1$, and running $w$ sends $d$ to zero. If $d_{i+1}+1<d_i$ for a cyclic index $i$, then
--
--   $$
--   \exists v:\quad p(i\ i+1)\operatorname{ev}(v)=1,\quad |v|+1=|w|,\quad\#_L(v)=\#_L(w).
--   $$
--
--   An initial descending pair forces a removable exchange in any exact sorting word.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AdjacentDeletion.lean#L8-L50

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
namespace LX.LiftedScan
end LX.LiftedScan
namespace List
end List

namespace LX.LiftedScan
end LX.LiftedScan
open LX
open LX.LiftedScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.LiftedScan.delete_adjacent_descent (hn : 2 ≤ n) (p : State n) (d : Fin n → ℤ)
    (w : List Letter) (hp : p*eval w=1) (hz : ∀ i,AffineScan.run w d i=0)
    (i : Fin n) (hdesc : d (i+1)+1 < d i) :
    ∃ v : List Letter,(p*Equiv.swap i (i+1))*eval v=1 ∧
      v.length+1=w.length ∧ v.count .l=w.count .l := by sorry

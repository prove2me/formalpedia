-- Prove2me | Theorems.Thm_LX_AffineScan_even_exception_paid_rotation_lower
-- name    : LX.AffineScan.even_exception_paid_rotation_lower
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:08:39.977715+00:00
-- url     : https://prove2.me/theorems/22399191-34b9-48db-a6eb-e548ab4a6c76
-- title:
--   Paid rotation lower bound for the exceptional even board
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For $n=2m$, define $e_0=4-m$, $e_1=e_2=1-m$, $e_i=m+4-2i$ for $3\le i\le m+1$, and $e_i=3m+4-2i$ for $m+2\le i<2m$. A balanced lift of a permutation $p$ with phase $c$ means $\sum_i d_i=0$ and $i+d_i\equiv p^{-1}(i)+c\pmod n$. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. A greedy scan compares the first two integer targets, exchanges a strict descent, and otherwise advances the cyclic cursor, stopping at the zero board. For its trace $g$, write $P_c(g)=\#_L(g)+((c-\#_L(g))\bmod n)$ for the paid rotation count. Let $m\ge3$, $n=2m$, and suppose $e$ is a balanced lift of some permutation at an integer phase. For any greedy trace $g$ of this board,
--
--   $$
--   (n-1)(m-2)+1+n\le P_{m+3}(g).
--   $$
--
--   The exceptional queue delay persists for every exact schedule, and its phase increases the paid bound where indicated.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ExceptionalPrefixDelay.lean#L135-L151

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
import Definitions.Def_LX_ExceptionalPrefixDelay
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_WordMetric

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
variable {n : ℕ} [NeZero n]

theorem LX.AffineScan.even_exception_paid_rotation_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (evenException (n := n) m))
    {g : List Letter} (hg : ScanTrace (evenException (n := n) m) g) :
    (n-1)*(m-2)+1+n ≤ paidRotations ((m+3 : ℕ) : Fin n) g := by sorry

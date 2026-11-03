-- Prove2me | Theorems.Thm_LX_length_lower_iff_greedy_prices
-- name    : LX.length_lower_iff_greedy_prices
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:09:32.058108+00:00
-- url     : https://prove2.me/theorems/9e87227a-67da-460d-a263-03d92c87867b
-- title:
--   Word-length lower bounds are equivalent to all greedy-price bounds
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For an integer board $d:I_n\to\mathbb Z$, put $F_i=i+d_i$, $\lambda_i=F_i\bmod n$, $C_{ij}=-\lfloor(((j-i)\bmod n)+d_j-d_i)/n\rfloor$, $B_i=\sum_j\max(-C_{ij},0)$, and $I(d)=\sum_{i<j}|\lfloor(F_j-F_i)/n\rfloor|$. A balanced lift of a permutation $p$ with phase $c$ means $\sum_i d_i=0$ and $i+d_i\equiv p^{-1}(i)+c\pmod n$. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. A greedy scan compares the first two integer targets, exchanges a strict descent, and otherwise advances the cyclic cursor, stopping at the zero board. For its trace $g$, write $P_c(g)=\#_L(g)+((c-\#_L(g))\bmod n)$ for the paid rotation count. Let $n\ge2$, let $p$ permute $I_n$, let $B\in\mathbb N$, and let $\ell(p)$ denote its shortest generator length. Then
--
--   $$
--   B\le\ell(p)\iff\forall c\in\mathbb N,\ \forall d,g:\ d\text{ lifts }p\text{ at }c,\ g\text{ is a greedy trace}\Rightarrow B\le I(d)+P_{c\bmod n}(g).
--   $$
--
--   The reduction ranges over every balanced lift and phase, giving an exact criterion for a metric lower bound.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/GreedyPriceCharacterization.lean#L26-L43

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
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_ScanInversions
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
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.LiftedScan
end LX.LiftedScan
namespace List
end List

namespace LX
end LX
open LX
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.length_lower_iff_greedy_prices (hn : 2 ≤ n) (p : State n) (B : ℕ) :
    B ≤ length p ↔ ∀ (c : ℕ) (d : Fin n → ℤ) (g : List Letter),
      IsLift p (c : ℤ) d → ScanTrace d g →
        B ≤ inversions d+paidRotations (c : Fin n) g := by sorry

-- Prove2me | Theorems.Thm_LX_AffineScan_ScanTrace_paid_length_le_any_word
-- name    : LX.AffineScan.ScanTrace.paid_length_le_any_word
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:03:03.343281+00:00
-- url     : https://prove2.me/theorems/6e2713c1-5127-463d-85e2-5a530eb8c12f
-- title:
--   The paid greedy trace is no longer than any exact word
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For an integer board $d:I_n\to\mathbb Z$, put $F_i=i+d_i$, $\lambda_i=F_i\bmod n$, $C_{ij}=-\lfloor(((j-i)\bmod n)+d_j-d_i)/n\rfloor$, $B_i=\sum_j\max(-C_{ij},0)$, and $I(d)=\sum_{i<j}|\lfloor(F_j-F_i)/n\rfloor|$. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. A greedy scan compares the first two integer targets, exchanges a strict descent, and otherwise advances the cyclic cursor, stopping at the zero board. For its trace $g$, write $P_c(g)=\#_L(g)+((c-\#_L(g))\bmod n)$ for the paid rotation count. Let $n\ge2$, let $d$ be balanced with distinct residue labels, and let $g$ be its greedy trace. If running $w$ sends $d$ to zero, put $c=\#_L(w)\bmod n$. Then
--
--   $$
--   |gL^{[c-\#_L(g)]_n}|\le|w|.
--   $$
--
--   Greedy normalization preserves the endpoint phase while improving or preserving literal length.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/GreedyWordNormalForm.lean#L31-L48

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

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AffineScan.ScanTrace.paid_length_le_any_word (hn : 2 ≤ n) {d : Fin n → ℤ}
    {g : List Letter} (hg : ScanTrace d g) (hb : ∑ i,d i=0)
    (hi : Function.Injective (labels d)) (w : List Letter) (hw : ∀ i,run w d i=0) :
    (paidWord (w.count .l : Fin n) g).length ≤ w.length := by sorry

-- Prove2me | Theorems.Thm_LX_Antipode_even_bottom_ordinary_paid
-- name    : LX.Antipode.even_bottom_ordinary_paid
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:01:08.802405+00:00
-- url     : https://prove2.me/theorems/12682d93-1b78-4416-b86d-010b186edc7e
-- title:
--   Ordinary bottom tokens pay the even target
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Define the candidate $p_{\mathrm e}=((i\mapsto1-i)\circ(1\ 2))^{-1}$. For an integer board $d:I_n\to\mathbb Z$, put $F_i=i+d_i$, $\lambda_i=F_i\bmod n$, $C_{ij}=-\lfloor(((j-i)\bmod n)+d_j-d_i)/n\rfloor$, $B_i=\sum_j\max(-C_{ij},0)$, and $I(d)=\sum_{i<j}|\lfloor(F_j-F_i)/n\rfloor|$. A balanced lift of a permutation $p$ with phase $c$ means $\sum_i d_i=0$ and $i+d_i\equiv p^{-1}(i)+c\pmod n$. A greedy scan compares the first two integer targets, exchanges a strict descent, and otherwise advances the cyclic cursor, stopping at the zero board. For its trace $g$, write $P_c(g)=\#_L(g)+((c-\#_L(g))\bmod n)$ for the paid rotation count. Let $m\ge3$, $n=2m$, let $d$ lift $p_{\mathrm e}$ with phase $c\in I_n$, and let $g$ be a greedy scan trace from $d$. If $i\ge3$ and $d_i=-m$,
--
--   $$
--   3m^2-4m+3\le I(d)+P_c(g).
--   $$
--
--   This isolates the exceptional geometry in the even-candidate lower bound.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AntipodeBoundaryPhase.lean#L54-L91

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
import Definitions.Def_LX_AntipodeCandidates
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Antipode
end LX.Antipode
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.LiftedScan
end LX.LiftedScan
namespace List
end List

namespace LX.Antipode
end LX.Antipode
open LX
open LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

theorem LX.Antipode.even_bottom_ordinary_paid (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift even (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) (i : Fin n) (hi : 3 ≤ i.val)
    (hdi : d i= -(m : ℤ)) :
    3*m^2-4*m+3 ≤ inversions d+paidRotations c g := by sorry

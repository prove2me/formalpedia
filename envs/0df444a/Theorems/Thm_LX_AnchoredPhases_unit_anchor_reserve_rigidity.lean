-- Prove2me | Theorems.Thm_LX_AnchoredPhases_unit_anchor_reserve_rigidity
-- name    : LX.AnchoredPhases.unit_anchor_reserve_rigidity
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:01:27.640919+00:00
-- url     : https://prove2.me/theorems/4b841fa6-38ab-44f6-a56e-3503c57036a3
-- title:
--   Rigidity of unit anchor reserve
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For a permutation $p$ and anchor $a$, let $q_a(i)=p(i)+a-p(a)$, $h_a=|\{i:q_a(i)<i\}|$, $D^a_i=((q_a(i)-i)\bmod n)-h_a$, and $c_a=a-p(a)-h_a$. A board is majorized if $2\sum_{i\in S}d_i\le |S|(n-|S|)$ for every subset $S\subseteq I_n$. Assume $n>0$ and $D^a$ is majorized. Write $s=|\operatorname{supp}(q_a)|$, $k$ for its number of nontrivial cycles, $\Delta=\sum_i|q_a(i)-i|-\operatorname{inv}(q_a)-s+k$, and $A=h_a(n-h_a-1)-I(D^a)$. If $A=1$, then
--
--   $$
--   \Delta=0,\quad s-k=h_a+1,\quad 2h_a\le s\le2h_a+2,\quad s-2k\le2.
--   $$
--
--   Unit reserve severely restricts the excess cycle size beyond disjoint transpositions.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AnchorReserveRigidity.lean#L66-L86

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
import Definitions.Def_LX_AnchorReserveRigidity
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_TwoWindowCycleDefect
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
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.unit_anchor_reserve_rigidity (p : State n) (a : Fin n)
    (hmaj : Majorized (_root_.LX.AnchoredPhases.displacement p a)) (hunit : anchorReserve p a=1) :
    LX.Core.FiniteCuts.cycleDefect (permutation p a)=0 ∧
      ((permutation p a).support.card : ℤ)-(permutation p a).cycleFactorsFinset.card=
        (height p a : ℤ)+1 ∧
      2*(height p a : ℤ) ≤ (permutation p a).support.card ∧
      ((permutation p a).support.card : ℤ) ≤ 2*height p a+2 ∧
      ((permutation p a).support.card : ℤ)-2*(permutation p a).cycleFactorsFinset.card ≤ 2 := by sorry

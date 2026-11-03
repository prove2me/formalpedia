-- Prove2me | Theorems.Thm_LX_AnchoredPhases_even_reflection_sharp_crossing_choice
-- name    : LX.AnchoredPhases.even_reflection_sharp_crossing_choice
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:18:19.919466+00:00
-- url     : https://prove2.me/theorems/af92c286-3ba2-4fa8-905b-29a2ea0bf767
-- title:
--   A crossing anchor for an even reflection
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For a permutation $p$ and anchor $a$, let $q_a(i)=p(i)+a-p(a)$, $h_a=|\{i:q_a(i)<i\}|$, $D^a_i=((q_a(i)-i)\bmod n)-h_a$, and $c_a=a-p(a)-h_a$. Put $u_i=[p(i)-i-(p(a)-a)]_n$, $N_a(t)=|\{i:u_i<t\}|$, $S_a(t)=N_a(t)-t$, and $E_a=\sum_{t=0}^{n-1}\max(S_a(t)-2,0)$. A global minimum anchor minimizes $\sum_i d_i^2$ over all balanced lifts of $p^{-1}$ and all phases. Let $p(j)=r-j$ modulo $n$, let $i\in I_n$, and suppose $n=2m$ with $m\ge4$. Then
--
--   $$
--   \big(\exists a:\ m<a,\ a+[-p(a)]_n\le n+3,\ u_i\ge2\big)\ \lor\ \big(r=0\land(i=1\lor i=m+1)\big).
--   $$
--
--   Here $u_i=[p(i)-i-(p(a)-a)]_n$ uses the chosen anchor. The two exceptional positions are isolated explicitly.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/EvenReflectionSharpChoice.lean#L44-L116

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
import Definitions.Def_LX_MinimumHeightRanks
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
namespace LX.Core.FiniteCoordinates
end LX.Core.FiniteCoordinates
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
namespace LX.LiftedScan
end LX.LiftedScan
namespace LX.PairCore
end LX.PairCore
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.even_reflection_sharp_crossing_choice (p : State n) (r i : Fin n)
    (hp : ∀ j,p j=r-j) (m : ℕ) (hn : n=2*m) (hm : 4 ≤ m) :
    (∃ a : Fin n,m < a.val ∧ a.val+(-p a).val ≤ n+3 ∧
      2 ≤ (cyclicOffset p a i).val) ∨
      (r=0 ∧ (i.val=1 ∨ i.val=m+1)) := by sorry

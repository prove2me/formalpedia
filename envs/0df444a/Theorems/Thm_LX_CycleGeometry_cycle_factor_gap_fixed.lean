-- Prove2me | Theorems.Thm_LX_CycleGeometry_cycle_factor_gap_fixed
-- name    : LX.CycleGeometry.cycle_factor_gap_fixed
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:21:12.641878+00:00
-- url     : https://prove2.me/theorems/f3515749-79ff-40bd-b7bb-84ee009b6625
-- title:
--   A gap between consecutive cycle vertices contains a fixed point
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For a permutation $p$, put $M(p)=\sum_i|p(i)-i|$, $s(p)=|\operatorname{supp}(p)|$, $k(p)$ equal to the number of nontrivial cycles, and $\Delta(p)=M(p)-\operatorname{inv}(p)-s(p)+k(p)$. Let $n>0$, suppose $\Delta(q)=0$ and $|q(i)-i|\ne1$ for every $i$. Let $g$ be a nontrivial cycle factor of $q$, let $a,c$ belong to its support, and assume $a+1<c$ and no support vertex of $g$ lies strictly between them. Then
--
--   $$
--   \exists i:\quad a<i<c,\quad q(i)=i.
--   $$
--
--   An ordinary gap in one cycle support must contain a fixed vertex of the full permutation.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/InvariantCycleGap.lean#L65-L86

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
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_TwoWindowCycleDefect
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
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
namespace LX.CycleGeometry
end LX.CycleGeometry
namespace LX.EventGeometry
end LX.EventGeometry
namespace List
end List

namespace LX.CycleGeometry
end LX.CycleGeometry
open LX
open LX.CycleGeometry
open scoped BigOperators
open LX.Core.FiniteCuts LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem LX.CycleGeometry.cycle_factor_gap_fixed (q g : State n) (hq : cycleDefect q=0)
    (hunit : ∀ i : Fin n,|_root_.LX.Core.FiniteCuts.displacement q i| ≠ 1)
    (hg : g ∈ q.cycleFactorsFinset) (a c : Fin n)
    (ha : a ∈ g.support) (hc : c ∈ g.support) (hwidth : a.val+1 < c.val)
    (hgap : ∀ i : Fin n,a.val < i.val → i.val < c.val → i ∉ g.support) :
    ∃ i : Fin n,a.val < i.val ∧ i.val < c.val ∧ q i=i := by sorry

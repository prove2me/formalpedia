-- Prove2me | Theorems.Thm_LX_CycleGeometry_zero_defect_invariant_gap_fixed
-- name    : LX.CycleGeometry.zero_defect_invariant_gap_fixed
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:20:47.555335+00:00
-- url     : https://prove2.me/theorems/97d2da91-ae7c-4ed0-a1b2-ce690da09b07
-- title:
--   A zero-defect invariant gap contains a fixed point
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For a permutation $p$, put $M(p)=\sum_i|p(i)-i|$, $s(p)=|\operatorname{supp}(p)|$, $k(p)$ equal to the number of nontrivial cycles, and $\Delta(p)=M(p)-\operatorname{inv}(p)-s(p)+k(p)$. Let $n>0$, suppose $\Delta(q)=0$ and $|q(i)-i|\ne1$ for every $i$. Let $a<b<c$ and assume the open interval $(a,c)$ is invariant under $q$, meaning $a<q(i)<c\iff a<i<c$. Then
--
--   $$
--   \exists i:\quad a<i<c,\quad q(i)=i.
--   $$
--
--   An invariant nonempty gap cannot be filled entirely by moving vertices when unit arrows are absent.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/InvariantCycleGap.lean#L12-L63

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

theorem LX.CycleGeometry.zero_defect_invariant_gap_fixed (q : State n) (hq : cycleDefect q=0)
    (hunit : ∀ i : Fin n,|_root_.LX.Core.FiniteCuts.displacement q i| ≠ 1)
    (a c b : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val)
    (hinv : ∀ i : Fin n,(a.val < (q i).val ∧ (q i).val < c.val) ↔
      (a.val < i.val ∧ i.val < c.val)) :
    ∃ i : Fin n,a.val < i.val ∧ i.val < c.val ∧ q i=i := by sorry

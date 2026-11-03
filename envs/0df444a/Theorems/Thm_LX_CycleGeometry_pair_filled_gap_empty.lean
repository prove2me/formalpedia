-- Prove2me | Theorems.Thm_LX_CycleGeometry_pair_filled_gap_empty
-- name    : LX.CycleGeometry.pair_filled_gap_empty
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:22:31.197804+00:00
-- url     : https://prove2.me/theorems/803f576c-31fb-4b5d-a8bb-1ae56ba5c1f0
-- title:
--   A zero-defect interval filled only with moving involutive points cannot contain an interior point under the backward-neighbor exclusion
-- statement:
--   A zero-defect interval filled only with moving involutive points cannot contain an interior point under the backward-neighbor exclusion.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{Def}(p)=\sum_i|\Delta(p,i)|-\operatorname{inv}(p)-|\operatorname{supp}(p)|+|\operatorname{cycles}(p)|$ is cycle defect.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (q : \mathfrak S(I_n)), \operatorname{Def} q = 0 \to  \forall  (a c : I_{n}), (\forall  (b : I_{n}), \operatorname{rep}\,a < \operatorname{rep}\,b \to  \operatorname{rep}\,b < \operatorname{rep}\,c \to  \operatorname{rep}\,a < \operatorname{rep}\,(q b) \land  \operatorname{rep}\,(q b) < \operatorname{rep}\,c) \to  (\forall  (b : I_{n}), \operatorname{rep}\,a < \operatorname{rep}\,b \to  \operatorname{rep}\,b < \operatorname{rep}\,c \to  q (q b) = b) \to  (\forall  (b : I_{n}), \operatorname{rep}\,a < \operatorname{rep}\,b \to  \operatorname{rep}\,b < \operatorname{rep}\,c \to  q b \ne  b) \to  (\forall  (i j : I_{n}), \operatorname{rep}\,i + 1 = \operatorname{rep}\,j \to  q j \ne  i) \to  \operatorname{rep}\,c \le  \operatorname{rep}\,a + 1
--   $$
--
--   This supplies a local geometric constraint for the subsequent cycle and matching arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PairFilledCycleGaps.lean#L11-L46

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
namespace LX.CycleGeometry
end LX.CycleGeometry
namespace LX.EventGeometry
end LX.EventGeometry
namespace LX.PairCore
end LX.PairCore
namespace List
end List

namespace LX.CycleGeometry
end LX.CycleGeometry
open LX
open LX.CycleGeometry
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem LX.CycleGeometry.pair_filled_gap_empty (q : State n) (hq : cycleDefect q=0)
    (a c : Fin n)
    (hinv : ∀ b : Fin n,a.val < b.val → b.val < c.val →
      a.val < (q b).val ∧ (q b).val < c.val)
    (hpairs : ∀ b : Fin n,a.val < b.val → b.val < c.val → q (q b)=b)
    (hfixed : ∀ b : Fin n,a.val < b.val → b.val < c.val → q b ≠ b)
    (hback : ∀ i j : Fin n,i.val+1=j.val → q j ≠ i) : c.val ≤ a.val+1 := by sorry

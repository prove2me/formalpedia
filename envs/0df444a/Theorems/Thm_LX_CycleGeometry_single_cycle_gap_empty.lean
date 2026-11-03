-- Prove2me | Theorems.Thm_LX_CycleGeometry_single_cycle_gap_empty
-- name    : LX.CycleGeometry.single_cycle_gap_empty
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:22:08.36396+00:00
-- url     : https://prove2.me/theorems/5fdd290e-5d9f-404b-a3ec-fb2bd9da2145
-- title:
--   A gap in a distinguished cycle cannot be filled by nonfixed pair cycles when backward neighbors are excluded
-- statement:
--   A gap in a distinguished cycle cannot be filled by nonfixed pair cycles when backward neighbors are excluded.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\mathcal P_{\rm fin}(X)$ denotes finite subsets and a subscript $\#$ denotes cardinality. Function symbols are written in curried notation. $\mathrm{Def}(p)=\sum_i|\Delta(p,i)|-\operatorname{inv}(p)-|\operatorname{supp}(p)|+|\operatorname{cycles}(p)|$ is cycle defect. $\operatorname{supp}(p)$ is the moved-point set and $\operatorname{cycles}(p)$ its nontrivial disjoint cycle factors; cycle membership includes fixed singleton orbits.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (q g : \mathfrak S(I_n)), \operatorname{Def} q = 0 \to  g \in  \operatorname{cycles} q \to  (\forall  f \in  \operatorname{cycles} q, f \ne  g \to  f_{\rm supp}_{\#} = 2) \to  (\forall  (i j : I_{n}), \operatorname{rep}\,i + 1 = \operatorname{rep}\,j \to  q j \ne  i) \to  \forall  (a c : I_{n}), a \in  \operatorname{supp} g \to  c \in  \operatorname{supp} g \to  (\forall  (i : I_{n}), \operatorname{rep}\,a < \operatorname{rep}\,i \to  \operatorname{rep}\,i < \operatorname{rep}\,c \to  i \notin  \operatorname{supp} g) \to  (\forall  (i : I_{n}), \operatorname{rep}\,a < \operatorname{rep}\,i \to  \operatorname{rep}\,i < \operatorname{rep}\,c \to  q i \ne  i) \to  \operatorname{rep}\,c \le  \operatorname{rep}\,a + 1
--   $$
--
--   This supplies a local geometric constraint for the subsequent cycle and matching arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PairFilledCycleGaps.lean#L66-L91

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

theorem LX.CycleGeometry.single_cycle_gap_empty (q g : State n) (hq : cycleDefect q=0)
    (hg : g ∈ q.cycleFactorsFinset)
    (hother : ∀ f ∈ q.cycleFactorsFinset,f ≠ g → f.support.card=2)
    (hback : ∀ i j : Fin n,i.val+1=j.val → q j ≠ i)
    (a c : Fin n) (ha : a ∈ g.support) (hc : c ∈ g.support)
    (hgap : ∀ i : Fin n,a.val < i.val → i.val < c.val → i ∉ g.support)
    (hfixed : ∀ i : Fin n,a.val < i.val → i.val < c.val → q i ≠ i) :
    c.val ≤ a.val+1 := by sorry

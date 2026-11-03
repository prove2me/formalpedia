-- Prove2me | Theorems.Thm_LX_CycleGeometry_outside_single_cycle_involutive
-- name    : LX.CycleGeometry.outside_single_cycle_involutive
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:21:36.477996+00:00
-- url     : https://prove2.me/theorems/c1197174-fa5f-4ded-9df3-cdf1c62f8968
-- title:
--   Outside a distinguished cycle, a permutation whose other cycles are pairs is involutive
-- statement:
--   Outside a distinguished cycle, a permutation whose other cycles are pairs is involutive.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\mathcal P_{\rm fin}(X)$ denotes finite subsets and a subscript $\#$ denotes cardinality. Function symbols are written in curried notation. $\operatorname{supp}(p)$ is the moved-point set and $\operatorname{cycles}(p)$ its nontrivial disjoint cycle factors; cycle membership includes fixed singleton orbits.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (q g : \mathfrak S(I_n)), g \in  \operatorname{cycles} q \to  (\forall  f \in  \operatorname{cycles} q, f \ne  g \to  f_{\rm supp}_{\#} = 2) \to  \forall  i \notin  \operatorname{supp} g, q (q i) = i
--   $$
--
--   This supplies a local geometric constraint for the subsequent cycle and matching arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PairFilledCycleGaps.lean#L48-L64

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

theorem LX.CycleGeometry.outside_single_cycle_involutive (q g : State n)
    (hg : g ∈ q.cycleFactorsFinset)
    (hother : ∀ f ∈ q.cycleFactorsFinset,f ≠ g → f.support.card=2)
    (i : Fin n) (hi : i ∉ g.support) : q (q i)=i := by sorry

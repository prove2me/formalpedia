-- Prove2me | Theorems.Thm_LX_AnchoredPhases_small_cycle_excess_profile
-- name    : LX.AnchoredPhases.small_cycle_excess_profile
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:22:51.389922+00:00
-- url     : https://prove2.me/theorems/efaf52cc-eeca-4fe6-b574-4dfdc5814c10
-- title:
--   Cycle profile when total excess is at most two
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Let $n>0$, let $q$ have $k$ nontrivial cycles, and let $0\le e\le2$ satisfy $|\operatorname{supp}(q)|=2k+e$. Write $c_j$ for the number of its cycles of size $j$. Then
--
--   $$
--   \text{every nontrivial cycle has size }2,3,\text{ or }4,\qquad c_3+2c_4=e.
--   $$
--
--   At most two excess vertices permit only triangles and quadrilaterals beyond transposition cycles.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/EvenUnitStructure.lean#L115-L138

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
import Definitions.Def_LX_EvenUnitStructure
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
namespace LX.PairCore
end LX.PairCore
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.small_cycle_excess_profile (q : State n) (e : ℕ) (he2 : e ≤ 2)
    (he : q.support.card=2*q.cycleFactorsFinset.card+e) :
    (∀ g ∈ q.cycleFactorsFinset,g.support.card=2 ∨ g.support.card=3 ∨ g.support.card=4) ∧
      cycleSizeCount q 3+2*cycleSizeCount q 4=e := by sorry

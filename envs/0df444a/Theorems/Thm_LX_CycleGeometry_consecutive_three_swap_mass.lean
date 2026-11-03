-- Prove2me | Theorems.Thm_LX_CycleGeometry_consecutive_three_swap_mass
-- name    : LX.CycleGeometry.consecutive_three_swap_mass
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:22:44.457866+00:00
-- url     : https://prove2.me/theorems/6decfd6d-84b1-431c-9da9-f1ffc8624640
-- title:
--   Swapping the first two sources of a consecutive forward three-chain preserves total absolute displacement
-- statement:
--   Swapping the first two sources of a consecutive forward three-chain preserves total absolute displacement.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\Delta(p,i)=\operatorname{rep}(p(i))-\operatorname{rep}(i)$ is ordinary integer displacement.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (q : \mathfrak S(I_n)) (a b c : I_{n}), \operatorname{rep}\,a + 1 = \operatorname{rep}\,b \to  \operatorname{rep}\,b + 1 = \operatorname{rep}\,c \to  q a = b \to  q b = c \to  \sum_{i} |\Delta (q\, \operatorname{swap} a b) i| = \sum_{i} |\Delta q i|
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/SingleThreeReflection.lean#L9-L30

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
namespace LX.FiniteJoin
end LX.FiniteJoin
namespace LX.PairCore
end LX.PairCore
namespace List
end List

namespace LX.CycleGeometry
end LX.CycleGeometry
open LX
open LX.CycleGeometry
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem LX.CycleGeometry.consecutive_three_swap_mass (q : State n) (a b c : Fin n)
    (hab : a.val+1=b.val) (hbc : b.val+1=c.val) (ha : q a=b) (hb : q b=c) :
    (∑ i, |_root_.LX.Core.FiniteCuts.displacement (q*Equiv.swap a b) i|)=∑ i, |_root_.LX.Core.FiniteCuts.displacement q i| := by sorry

-- Prove2me | Theorems.Thm_LX_AnchoredPhases_odd_reflection_neighbor_fiber
-- name    : LX.AnchoredPhases.odd_reflection_neighbor_fiber
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:23:30.543445+00:00
-- url     : https://prove2.me/theorems/d2451fae-d14d-4ea4-ad62-2b5a7c0233a9
-- title:
--   Undoing an adjacent swap in an odd reflection creates an exact three-position raw-offset fiber
-- statement:
--   Undoing an adjacent swap in an odd reflection creates an exact three-position raw-offset fiber.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (r u : I_{n}), (\forall  (i : I_{n}), (p\, \operatorname{swap} u (u + 1)) i = r - i) \to  \forall  (m : \mathbb N), n = 2\, m + 1 \to  2 \le  m \to  \forall  (i : I_{n}), p i - i = p u - u \Longleftrightarrow  i = u \lor  i = u + 1 \lor  i = u + \operatorname{rep}\,(m + 1)
--   $$
--
--   This supplies a local geometric constraint for the subsequent cycle and matching arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/OddReflectionNeighborFiber.lean#L9-L61

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
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.odd_reflection_neighbor_fiber (p : State n) (r u : Fin n)
    (hp : ∀ i,(p*Equiv.swap u (u+1)) i=r-i)
    (m : ℕ) (hn : n=2*m+1) (hm : 2 ≤ m) (i : Fin n) :
    p i-i=p u-u ↔ i=u ∨ i=u+1 ∨ i=u+((m+1 : ℕ) : Fin n) := by sorry

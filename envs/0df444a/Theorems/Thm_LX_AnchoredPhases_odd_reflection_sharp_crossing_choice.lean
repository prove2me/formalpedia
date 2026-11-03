-- Prove2me | Theorems.Thm_LX_AnchoredPhases_odd_reflection_sharp_crossing_choice
-- name    : LX.AnchoredPhases.odd_reflection_sharp_crossing_choice
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:23:16.857781+00:00
-- url     : https://prove2.me/theorems/5e9799b2-c49c-41bb-b654-e051d9a4de7d
-- title:
--   An odd reflection offers a sharp crossing anchor except in two explicitly retained families
-- statement:
--   An odd reflection offers a sharp crossing anchor except in two explicitly retained families.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $r(p,a,i)=p(i)-i-(p(a)-a)$ is the relative cyclic offset.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (r i : I_{n}), (\forall  (j : I_{n}), p j = r - j) \to  \forall  (m : \mathbb N), n = 2\, m + 1 \to  3 \le  m \to  (\exists  a, 0 < \operatorname{rep}\,a \land  \operatorname{rep}\,a + m \le  \operatorname{rep}\,(p a) + 2 \land  3 \le  \operatorname{rep}\,a + (n - \operatorname{rep}\,(p a)) \land  2 \le  \operatorname{rep}\,(r p a i)) \lor  \operatorname{rep}\,r = m \land  \operatorname{rep}\,i = m + 1 \lor  \operatorname{rep}\,r = m + 1 \land  \operatorname{rep}\,i = 1
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/OddReflectionSharpChoice.lean#L10-L99

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
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.odd_reflection_sharp_crossing_choice (p : State n) (r i : Fin n)
    (hp : ∀ j,p j=r-j) (m : ℕ) (hn : n=2*m+1) (hm : 3 ≤ m) :
    (∃ a : Fin n,0 < a.val ∧ a.val+m ≤ (p a).val+2 ∧
      3 ≤ a.val+(n-(p a).val) ∧ 2 ≤ (cyclicOffset p a i).val) ∨
      (r.val=m ∧ i.val=m+1) ∨ (r.val=m+1 ∧ i.val=1) := by sorry

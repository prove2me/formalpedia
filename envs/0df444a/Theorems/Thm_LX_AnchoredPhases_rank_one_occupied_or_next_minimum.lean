-- Prove2me | Theorems.Thm_LX_AnchoredPhases_rank_one_occupied_or_next_minimum
-- name    : LX.AnchoredPhases.rank_one_occupied_or_next_minimum
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:17:15.466941+00:00
-- url     : https://prove2.me/theorems/79e88a80-0291-4e40-88aa-fde57b2b657c
-- title:
--   A rank-one offset is either occupied at the next height or followed by a minimum offset
-- statement:
--   A rank-one offset is either occupied at the next height or followed by a minimum offset.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $h(p,a)=|\{i:q(p,a)(i)<i\}|$ counts its ordinary descending arrows. $r(p,a,i)=p(i)-i-(p(a)-a)$ is the relative cyclic offset. $R(p,a,t)=B(p,a,t)-t$ is the integer rank surplus. $q(p,a)(i)=p(i)+a-p(a)$ is the anchored permutation, with arithmetic in the residue circle. $B(p,a,t)=|\{i:\operatorname{rep}(r(p,a,i))<t\}|$ counts offsets below the natural threshold.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (a t : I_{n}), (\forall  (b : I_{n}), h p a \le  h p b) \to  R p a \operatorname{rep}\,t = 1 \to  (\exists  b, r p a b = t \land  h p b = h p a + 1) \lor  \exists  b, r p a b = t + 1 \land  h p b = h p a
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/RankPeakCount.lean#L184-L218

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
import Definitions.Def_LX_AnchoredPhases
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
namespace LX.PairCore
end LX.PairCore
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.rank_one_occupied_or_next_minimum (p : State n) (a t : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (hone : rankSurplus p a t.val=1) :
    (∃ b : Fin n,cyclicOffset p a b=t ∧ height p b=height p a+1) ∨
      (∃ b : Fin n,cyclicOffset p a b=t+1 ∧ height p b=height p a) := by sorry

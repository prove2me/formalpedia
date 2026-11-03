-- Prove2me | Theorems.Thm_LX_AnchoredPhases_minimum_count_minus_high_count
-- name    : LX.AnchoredPhases.minimum_count_minus_high_count
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:17:47.1792+00:00
-- url     : https://prove2.me/theorems/fb7098c1-34e8-44dd-b454-6b1a4d77519c
-- title:
--   An attained rank peak forces a quadratic lower bound involving zero and high ranks
-- statement:
--   An attained rank peak forces a quadratic lower bound involving zero and high ranks.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $h(p,a)=|\{i:q(p,a)(i)<i\}|$ counts its ordinary descending arrows. $R(p,a,t)=B(p,a,t)-t$ is the integer rank surplus. $q(p,a)(i)=p(i)+a-p(a)$ is the anchored permutation, with arithmetic in the residue circle. $B(p,a,t)=|\{i:\operatorname{rep}(r(p,a,i))<t\}|$ counts offsets below the natural threshold. $r(p,a,i)=p(i)-i-(p(a)-a)$ is the relative cyclic offset.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (a r : I_{n}) (R : \mathbb N), (\forall  (b : I_{n}), h p a \le  h p b) \to  0 < R \to  R p a \operatorname{rep}\,r = \operatorname{rep}\,R \to  (\operatorname{rep}\,R - 1)\, (\operatorname{rep}\,R - 2) \le  2\, \operatorname{rep}\,\{t\mid R p a \operatorname{rep}\,t = 0\}_{\#} - 2\, \operatorname{rep}\,\{t\mid 2 \le  R p a \operatorname{rep}\,t\}_{\#} + \operatorname{rep}\,n\, (\operatorname{rep}\,n - 3 - 2\, \operatorname{rep}\,(h p a))
--   $$
--
--   This identity can be used while tracking the exact cost or structure of the sorting construction.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/RankPeakCount.lean#L141-L181

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

theorem LX.AnchoredPhases.minimum_count_minus_high_count (p : State n) (a r : Fin n) (R : ℕ)
    (hmin : ∀ b,height p a ≤ height p b)
    (hRpos : 0 < R) (hpeak : rankSurplus p a r.val=R) :
    ((R : ℤ)-1)*(R-2) ≤
      2*((Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card : ℤ)-
        2*((Finset.univ.filter (fun t : Fin n => 2 ≤ rankSurplus p a t.val)).card : ℤ)+
        (n : ℤ)*((n : ℤ)-3-2*height p a) := by sorry

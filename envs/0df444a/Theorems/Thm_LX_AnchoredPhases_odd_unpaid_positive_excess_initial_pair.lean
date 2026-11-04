-- Prove2me | Theorems.Thm_LX_AnchoredPhases_odd_unpaid_positive_excess_initial_pair
-- name    : LX.AnchoredPhases.odd_unpaid_positive_excess_initial_pair
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:28:51.985376+00:00
-- url     : https://prove2.me/theorems/81e5c7f5-a6f6-49d5-bb2a-520309a934a5
-- title:
--   Positive second excess forces the first two physical positions to be fixed
-- statement:
--   Positive second excess forces the first two physical positions to be fixed.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. An existential $w$ is a finite word in these generators. Natural subtraction is truncated at zero; scalar price expressions and quantities coerced by $\operatorname{rep}$ are read in the integers. The identity permutation is $1$. $h(p,a)=|\{i:q(p,a)(i)<i\}|$ counts its ordinary descending arrows. $R(p,a,t)=B(p,a,t)-t$ is the integer rank surplus. $Q(p,a)=\sum_{t\in I_n}\max(R(p,a,\operatorname{rep}(t))-2,0)$ is second excess. Words use forward rotation $l:i\mapsto i+1$ and adjacent exchange $x=(0\ 1)$; $\operatorname{ev}(w)$ is their ordered product. $q(p,a)(i)=p(i)+a-p(a)$ is the anchored permutation, with arithmetic in the residue circle. $B(p,a,t)=|\{i:\operatorname{rep}(r(p,a,i))<t\}|$ counts offsets below the natural threshold. $r(p,a,i)=p(i)-i-(p(a)-a)$ is the relative cyclic offset.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (a : I_{n}), n = 2\, h p a + 3 \to  2 \le  h p a \to  (\forall  (c : I_{n}), h p a \le  h p c) \to  (\forall  (t : I_{n}), R p a \operatorname{rep}\,t \le  3) \to  0 < Q p a \to  (\neg \exists  w, p\, \operatorname{ev} w = 1 \land  4\, \operatorname{rep}\,w_{\ell} \le  3\, \operatorname{rep}\,n ^{2} - 8\, \operatorname{rep}\,n + 9) \to  p 0 = 0 \land  p 1 = 1
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/OddPositiveExcessHead.lean#L34-L59

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
import Definitions.Def_LX_SecondExcess
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
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.PairCore
end LX.PairCore
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.odd_unpaid_positive_excess_initial_pair (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 3)
    (hpos : 0 < secondExcess p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : p 0=0 ∧ p 1=1 := by sorry

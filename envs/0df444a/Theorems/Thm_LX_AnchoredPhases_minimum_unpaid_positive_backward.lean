-- Prove2me | Theorems.Thm_LX_AnchoredPhases_minimum_unpaid_positive_backward
-- name    : LX.AnchoredPhases.minimum_unpaid_positive_backward
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:25:29.270599+00:00
-- url     : https://prove2.me/theorems/ce7d7e1b-9773-4b67-a8f7-4396def95c51
-- title:
--   A nonzero, non-head minimum offset in an unpaid input has a backward representative with nonzero image
-- statement:
--   A nonzero, non-head minimum offset in an unpaid input has a backward representative with nonzero image.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. An existential $w$ is a finite word in these generators. Natural subtraction is truncated at zero; scalar price expressions and quantities coerced by $\operatorname{rep}$ are read in the integers. The identity permutation is $1$. $h(p,a)=|\{i:q(p,a)(i)<i\}|$ counts its ordinary descending arrows. $\mathrm{Desc}(p)=\{i:p(i)<i\}$ denotes descents in representative order. Words use forward rotation $l:i\mapsto i+1$ and adjacent exchange $x=(0\ 1)$; $\operatorname{ev}(w)$ is their ordered product. $q(p,a)(i)=p(i)+a-p(a)$ is the anchored permutation, with arithmetic in the residue circle.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (a b : I_{n}), \forall  e \le  1, n = 2\, h p a + 2 + e \to  2 \le  h p a \to  (\forall  (c : I_{n}), h p a \le  h p c) \to  h p b = h p a \to  (\neg \exists  w, p\, \operatorname{ev} w = 1 \land  4\, \operatorname{rep}\,w_{\ell} \le  3\, \operatorname{rep}\,n ^{2} - 8\, \operatorname{rep}\,n + 12 - 3\, \operatorname{rep}\,e) \to  p b - b \ne  0 \to  p b - b \ne  p 0 \to  \exists  i \in  \operatorname{Desc} p, p i \ne  0 \land  p i - i = p b - b
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/MinimumOffsetCount.lean#L18-L43

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
import Definitions.Def_LX_FiniteDescentRank
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

theorem LX.AnchoredPhases.minimum_unpaid_positive_backward (p : State n) (a b : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c) (hb : height p b=height p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e)
    (ht0 : p b-b ≠ 0) (hth : p b-b ≠ p 0) :
    ∃ i : Fin n,i ∈ descendingPositions p ∧ p i ≠ 0 ∧ p i-i=p b-b := by sorry

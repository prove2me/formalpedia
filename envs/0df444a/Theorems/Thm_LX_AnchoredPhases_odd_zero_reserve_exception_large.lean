-- Prove2me | Theorems.Thm_LX_AnchoredPhases_odd_zero_reserve_exception_large
-- name    : LX.AnchoredPhases.odd_zero_reserve_exception_large
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:23:38.148929+00:00
-- url     : https://prove2.me/theorems/685c7674-316b-496f-b635-94d3851d4fe4
-- title:
--   The large exceptional reflection-neighbor families still attain the odd word bound
-- statement:
--   The large exceptional reflection-neighbor families still attain the odd word bound.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. An existential $w$ is a finite word in these generators. Natural subtraction is truncated at zero; scalar price expressions and quantities coerced by $\operatorname{rep}$ are read in the integers. The identity permutation is $1$. $h(p,a)=|\{i:q(p,a)(i)<i\}|$ counts its ordinary descending arrows. $q(p,a)(i)=p(i)+a-p(a)$ is the anchored permutation, with arithmetic in the residue circle. $A(p,a)=h(p,a)(n-h(p,a)-1)-I(d_A(p,a))$ is anchor reserve. $\mathrm{GM}(p,a)$ means that this anchor minimizes $\sum_i d(i)^2$ over all balanced lifts of $p^{-1}$ and all phases. Words use forward rotation $l:i\mapsto i+1$ and adjacent exchange $x=(0\ 1)$; $\operatorname{ev}(w)$ is their ordered product. $I(d)=J(i\mapsto\operatorname{rep}(i)+d(i))$ is the affine inversion count of a displacement vector. $J(F)=\sum_{i<j}|\lfloor(F(j)-F(i))/n\rfloor|$ is affine inversion count.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (a r u : I_{n}), \operatorname{GM} p a \to  A p a = 0 \to  \forall  (m : \mathbb N), n = 2\, m + 1 \to  h p a + 1 = m \to  4 \le  m \to  (q p a) u = u \to  (\forall  (i : I_{n}), (p\, \operatorname{swap} u (u + 1)) i = r - i) \to  \operatorname{rep}\,r = m \land  \operatorname{rep}\,u = m + 1 \lor  \operatorname{rep}\,r = m + 1 \land  \operatorname{rep}\,u = 1 \to  \exists  w, p\, \operatorname{ev} w = 1 \land  4\, \operatorname{rep}\,w_{\ell} \le  3\, \operatorname{rep}\,n ^{2} - 8\, \operatorname{rep}\,n + 9
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/OddZeroReserveExceptions.lean#L12-L95

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
import Definitions.Def_LX_AnchorReserveRigidity
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_MinimumEnergyPhases
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
namespace LX.PairCore
end LX.PairCore
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.odd_zero_reserve_exception_large (p : State n) (a r u : Fin n)
    (ha : GlobalMinimum p a) (hz : anchorReserve p a=0)
    (m : ℕ) (hn : n=2*m+1) (hh : height p a+1=m) (hm : 4 ≤ m)
    (hu : permutation p a u=u)
    (hp : ∀ i,(p*Equiv.swap u (u+1)) i=r-i)
    (hcase : (r.val=m ∧ u.val=m+1) ∨ (r.val=m+1 ∧ u.val=1)) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by sorry

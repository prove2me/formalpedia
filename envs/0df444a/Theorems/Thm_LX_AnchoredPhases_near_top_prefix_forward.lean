-- Prove2me | Theorems.Thm_LX_AnchoredPhases_near_top_prefix_forward
-- name    : LX.AnchoredPhases.near_top_prefix_forward
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:25:19.428254+00:00
-- url     : https://prove2.me/theorems/0347d58a-3273-4acc-8536-9918373e3390
-- title:
--   A near-top prefix is forward and every open arrow interval in it consists of fixed points
-- statement:
--   A near-top prefix is forward and every open arrow interval in it consists of fixed points.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $h(p,a)=|\{i:q(p,a)(i)<i\}|$ counts its ordinary descending arrows. $q(p,a)(i)=p(i)+a-p(a)$ is the anchored permutation, with arithmetic in the residue circle. $d_A(p,a)(i)=\operatorname{rep}(p(i)-i-(p(a)-a))-h(p,a)$ is the balanced anchored displacement. $\beta(d,i)=\sum_j\max(-C(d,i,j),0)$ is backward depth. $\mathrm{Forward}(p,r)$ means $i\le p(i)$ for $i<r$, with every position strictly between $i$ and $p(i)$ fixed. $C(d,i,j)=-\lfloor(\operatorname{rep}(j-i)+d(j)-d(i))/n\rfloor$ is signed affine crossing multiplicity.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (a : I_{n}) (r : \mathbb N), 2 \le  h p a \to  (q p a) 0 \ne  0 \to  (\forall  (i : I_{n}), \operatorname{rep}\,i < r \to  h p a - 1 \le  \beta (d_A p a) i) \to  \operatorname{Forward} (q p a) r
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/NearTopPrefixBound.lean#L11-L31

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
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_ForwardPrefixContraction
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
open LX.AffineScan LX.FiniteDropBudget LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.near_top_prefix_forward (p : State n) (a : Fin n) (r : ℕ)
    (hh : 2 ≤ height p a) (hhead : permutation p a 0 ≠ 0)
    (hpre : ∀ i : Fin n,i.val < r → height p a-1 ≤ backwardDepth (_root_.LX.AnchoredPhases.displacement p a) i) :
    ForwardPrefix (permutation p a) r := by sorry

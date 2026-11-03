-- Prove2me | Theorems.Thm_LX_AnchoredPhases_reflection_depth_positions_even
-- name    : LX.AnchoredPhases.reflection_depth_positions_even
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:18:17.597205+00:00
-- url     : https://prove2.me/theorems/c6164f68-dc13-4baf-bbfe-9682b0f1239e
-- title:
--   For an even reflection anchored after the midpoint, the head is not maximal-depth and maximal-depth sources occur no later than the anchor
-- statement:
--   For an even reflection anchored after the midpoint, the head is not maximal-depth and maximal-depth sources occur no later than the anchor.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $h(p,a)=|\{i:q(p,a)(i)<i\}|$ counts its ordinary descending arrows. $d_A(p,a)(i)=\operatorname{rep}(p(i)-i-(p(a)-a))-h(p,a)$ is the balanced anchored displacement. $\beta(d,i)=\sum_j\max(-C(d,i,j),0)$ is backward depth. $q(p,a)(i)=p(i)+a-p(a)$ is the anchored permutation, with arithmetic in the residue circle. $C(d,i,j)=-\lfloor(\operatorname{rep}(j-i)+d(j)-d(i))/n\rfloor$ is signed affine crossing multiplicity.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (r : I_{n}), (\forall  (i : I_{n}), p i = r - i) \to  \forall  (m : \mathbb N), n = 2\, m \to  2 \le  m \to  \forall  (a : I_{n}), m < \operatorname{rep}\,a \to  \beta (d_A p a) 0 < h p a \land  \forall  (i : I_{n}), \beta (d_A p a) i = h p a \to  \operatorname{rep}\,i \le  \operatorname{rep}\,a
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ReflectionPhases.lean#L102-L132

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
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.reflection_depth_positions_even (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (m : ℕ) (hn : n=2*m) (hm : 2 ≤ m)
    (a : Fin n) (ha : m < a.val) :
    backwardDepth (_root_.LX.AnchoredPhases.displacement p a) 0 < height p a ∧
      ∀ i,backwardDepth (_root_.LX.AnchoredPhases.displacement p a) i=height p a → i.val ≤ a.val := by sorry

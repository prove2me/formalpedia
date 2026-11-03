-- Prove2me | Theorems.Thm_LX_AnchoredPhases_next_occupied_phase_with_order
-- name    : LX.AnchoredPhases.next_occupied_phase_with_order
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:24:36.888194+00:00
-- url     : https://prove2.me/theorems/1b70aa20-922c-4748-a233-24cf055035a4
-- title:
--   The next occupied raw-offset phase has exact height and inversion changes
-- statement:
--   The next occupied raw-offset phase has exact height and inversion changes.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $h(p,a)=|\{i:q(p,a)(i)<i\}|$ counts its ordinary descending arrows. $q(p,a)(i)=p(i)+a-p(a)$ is the anchored permutation, with arithmetic in the residue circle. $d_A(p,a)(i)=\operatorname{rep}(p(i)-i-(p(a)-a))-h(p,a)$ is the balanced anchored displacement. $r(p,a,i)=p(i)-i-(p(a)-a)$ is the relative cyclic offset. $I(d)=J(i\mapsto\operatorname{rep}(i)+d(i))$ is the affine inversion count of a displacement vector. $\mathrm{Fix}(p)=\{i:p(i)=i\}$ denotes fixed positions. $J(F)=\sum_{i<j}|\lfloor(F(j)-F(i))/n\rfloor|$ is affine inversion count.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (a : I_{n}), 0 < h p a \to  \text{put }f := (\operatorname{Fix} (q p a))_{\#}; \exists  b t, 0 < t \land  t < n \land  (\forall  (i : I_{n}), 0 < \operatorname{rep}\,(r p a i) \to  t \le  \operatorname{rep}\,(r p a i)) \land  p b - b = p a - a + \operatorname{rep}\,t \land  \operatorname{rep}\,(h p b) = \operatorname{rep}\,(h p a) + \operatorname{rep}\,f - \operatorname{rep}\,t \land  \operatorname{rep}\,(I (d_A p b)) - \operatorname{rep}\,(I (d_A p a)) = \operatorname{rep}\,f\, (\operatorname{rep}\,n - 2\, \operatorname{rep}\,(h p a) - \operatorname{rep}\,f)
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/NextOccupiedPhase.lean#L13-L110

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
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_ScanInversions
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
open LX.AffineScan LX.Core.AffineLift LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.next_occupied_phase_with_order (p : State n) (a : Fin n) (hh : 0 < height p a) :
    let f := (fixedPositions (permutation p a)).card
    ∃ b : Fin n,∃ t : ℕ,0 < t ∧ t < n ∧
      (∀ i : Fin n,0 < (cyclicOffset p a i).val → t ≤ (cyclicOffset p a i).val) ∧
      p b-b=p a-a+(t : Fin n) ∧
      (height p b : ℤ)=(height p a : ℤ)+f-t ∧
      (inversions (_root_.LX.AnchoredPhases.displacement p b) : ℤ)-inversions (_root_.LX.AnchoredPhases.displacement p a)=
        (f : ℤ)*((n : ℤ)-2*height p a-f) := by sorry

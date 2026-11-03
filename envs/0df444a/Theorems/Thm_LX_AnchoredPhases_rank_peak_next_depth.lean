-- Prove2me | Theorems.Thm_LX_AnchoredPhases_rank_peak_next_depth
-- name    : LX.AnchoredPhases.rank_peak_next_depth
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:18:15.024094+00:00
-- url     : https://prove2.me/theorems/0f0f13a9-e94d-46ae-af1a-47dfd24adb49
-- title:
--   A rank cap also bounds the count at one level below maximum depth
-- statement:
--   A rank cap also bounds the count at one level below maximum depth.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $h(p,a)=|\{i:q(p,a)(i)<i\}|$ counts its ordinary descending arrows. $d_A(p,a)(i)=\operatorname{rep}(p(i)-i-(p(a)-a))-h(p,a)$ is the balanced anchored displacement. $R(p,a,t)=B(p,a,t)-t$ is the integer rank surplus. $N(d,k)=|\{i:\beta(d,i)\ge k\}|$ counts tokens at or above depth $k$. $q(p,a)(i)=p(i)+a-p(a)$ is the anchored permutation, with arithmetic in the residue circle. $B(p,a,t)=|\{i:\operatorname{rep}(r(p,a,i))<t\}|$ counts offsets below the natural threshold. $\beta(d,i)=\sum_j\max(-C(d,i,j),0)$ is backward depth. $r(p,a,i)=p(i)-i-(p(a)-a)$ is the relative cyclic offset. $C(d,i,j)=-\lfloor(\operatorname{rep}(j-i)+d(j)-d(i))/n\rfloor$ is signed affine crossing multiplicity.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (a : I_{n}) (R : \mathbb N), (\forall  (t : I_{n}), R p a \operatorname{rep}\,t \le  \operatorname{rep}\,R) \to  \forall  (b : I_{n}), 0 < h p b \to  \operatorname{rep}\,(N (d_A p b) (h p b - 1)) + 2\, \operatorname{rep}\,(h p b) \le  2\, \operatorname{rep}\,(h p a) + 2\, \operatorname{rep}\,R + 3
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/RankProfileGeometry.lean#L70-L92

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
import Definitions.Def_LX_DepthCrowding
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

theorem LX.AnchoredPhases.rank_peak_next_depth (p : State n) (a : Fin n) (R : ℕ)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R)
    (b : Fin n) (hh : 0 < height p b) :
    (depthCount (_root_.LX.AnchoredPhases.displacement p b) (height p b-1) : ℤ)+2*height p b ≤
      2*(height p a : ℤ)+2*R+3 := by sorry

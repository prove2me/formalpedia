-- Prove2me | Theorems.Thm_LX_AffineScan_displacement_depth_width_bound
-- name    : LX.AffineScan.displacement_depth_width_bound
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:04:59.126204+00:00
-- url     : https://prove2.me/theorems/fe77fe36-2568-4c0e-b398-7a5a9e50fa4d
-- title:
--   In a width-n lift, a token's displacement plus depth is bounded by the next-depth count
-- statement:
--   In a width-n lift, a token's displacement plus depth is bounded by the next-depth count.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{Lift}(p,c,d)$ means $\sum_i d(i)=0$ and $i+d(i)\equiv p^{-1}(i)+c\pmod n$ for every residue $i$. $\beta(d,i)=\sum_j\max(-C(d,i,j),0)$ is backward depth. $N(d,k)=|\{i:\beta(d,i)\ge k\}|$ counts tokens at or above depth $k$. $C(d,i,j)=-\lfloor(\operatorname{rep}(j-i)+d(j)-d(i))/n\rfloor$ is signed affine crossing multiplicity.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (c : \mathbb Z) (d : I_{n} \to  \mathbb Z), \operatorname{Lift} p c d \to  (\forall  (i j : I_{n}), d i - d j \le  \operatorname{rep}\,n) \to  \forall  (k : \mathbb N) (i : I_{n}), k \le  \beta d i \to  d i + \operatorname{rep}\,(\beta d i) \le  \operatorname{rep}\,(N d (k + 1))
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/NearMinimumPhases.lean#L23-L40

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
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_DepthCrowding
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
namespace List
end List

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AffineScan.displacement_depth_width_bound {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (hwidth : ∀ i j,d i-d j ≤ (n : ℤ))
    (k : ℕ) (i : Fin n) (hk : k ≤ backwardDepth d i) :
    d i+(backwardDepth d i : ℤ) ≤ depthCount d (k+1) := by sorry

-- Prove2me | Theorems.Thm_LX_AffineScan_scan_deadline_of_prefix_bound
-- name    : LX.AffineScan.scan_deadline_of_prefix_bound
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:21:29.009842+00:00
-- url     : https://prove2.me/theorems/d2c940f0-84c0-440d-a85e-170c6b6e4165
-- title:
--   Bounds on maximal-depth positions and near-top prefixes control the scan deadline
-- statement:
--   Bounds on maximal-depth positions and near-top prefixes control the scan deadline.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\beta(d,i)=\sum_j\max(-C(d,i,j),0)$ is backward depth. $\lambda(d)(i)=i+d(i)\pmod n$ is its target residue. $b_t(d,j)=\beta(d,j\bmod n)$ is depth at that cursor slot. $K_s(d)=(n-1)+K_q(\mathrm{Sweep}(d,n-1))-1$ is the scan deadline, using natural subtraction. $C(d,i,j)=-\lfloor(\operatorname{rep}(j-i)+d(j)-d(i))/n\rfloor$ is signed affine crossing multiplicity.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) , 2 \le  n \to  \forall  (d : I_{n} \to  \mathbb Z), \operatorname{Inj} (\lambda d) \to  \forall  (h M K : \mathbb N), 2 \le  h \to  (\forall  (i : I_{n}), \beta d i \le  h) \to  \beta d 0 < h \to  (\forall  (i : I_{n}), \beta d i = h \to  \operatorname{rep}\,i \le  M) \to  (\forall  j \le  n, (\forall  i < j, h - 1 \le  \operatorname{bt} d i) \to  j \le  K) \to  K_s d \le  (h - 1)\, (n - 1) + \operatorname{max} M K - 1
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PrefixGapDeadline.lean#L44-L86

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
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_DeadlinePrice
import Definitions.Def_LX_DepthReturn

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

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.AffineScan.scan_deadline_of_prefix_bound (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (h M K : ℕ) (hpos : 2 ≤ h)
    (hmax : ∀ i, backwardDepth d i ≤ h) (hhead : backwardDepth d 0 < h)
    (hpositions : ∀ i, backwardDepth d i=h → i.val ≤ M)
    (hprefix : ∀ j ≤ n,(∀ i < j,h-1 ≤ atDepth d i) → j ≤ K) :
    scanDeadline d ≤ (h-1)*(n-1)+max M K-1 := by sorry

-- Prove2me | Theorems.Thm_LX_AffineScan_scan_deadline_le_any_word
-- name    : LX.AffineScan.scan_deadline_le_any_word
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:08:39.120014+00:00
-- url     : https://prove2.me/theorems/21f15baa-fe8c-4398-a097-93da1e97d8b1
-- title:
--   Every word ending at zero displacement needs at least the scan deadline's rotations when the first-lap queue is nonempty
-- statement:
--   Every word ending at zero displacement needs at least the scan deadline's rotations when the first-lap queue is nonempty.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. $\lambda(d)(i)=i+d(i)\pmod n$ is its target residue. $\mathrm{Run}(w,d)$ applies these rotation and exchange updates successively. $K_q(d)=\max_i[\,0\text{ if }\beta(d,i)=0;\ (n-1)(\beta(d,i)-1)+\operatorname{rep}(i)\text{ otherwise}\,]$ is the queue deadline. $K_s(d)=(n-1)+K_q(\mathrm{Sweep}(d,n-1))-1$ is the scan deadline, using natural subtraction. $\mathrm{Sweep}(d,k)$ repeats head comparison followed by rotation $k$ times.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) , 2 \le  n \to  \forall  (d : I_{n} \to  \mathbb Z), \sum_{i} d i = 0 \to  \operatorname{Inj} (\lambda d) \to  0 < K_q (\operatorname{Sweep} d (n - 1)) \to  \forall  (w : \operatorname{Seq} \mathcal A), (\forall  (i : I_{n}), \operatorname{Run} w d i = 0) \to  K_s d \le  \operatorname{count} l w
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/QueueDeadlineLower.lean#L92-L115

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
import Definitions.Def_LX_DeadlinePrice
import Definitions.Def_LX_SweepCarrier
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

theorem LX.AffineScan.scan_deadline_le_any_word (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i,d i=0) (hi : Function.Injective (labels d))
    (hq : 0 < queueDeadline (sweep d (n-1))) (w : List Letter)
    (hw : ∀ i,run w d i=0) : scanDeadline d ≤ w.count .l := by sorry

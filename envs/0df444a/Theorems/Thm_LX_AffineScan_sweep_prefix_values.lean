-- Prove2me | Theorems.Thm_LX_AffineScan_sweep_prefix_values
-- name    : LX.AffineScan.sweep_prefix_values
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:06:02.413648+00:00
-- url     : https://prove2.me/theorems/0c7dc026-d276-4ce1-be06-3293622c53c8
-- title:
--   During the first lap, the sweep head is the running carrier and untouched tail targets are translated
-- statement:
--   During the first lap, the sweep head is the running carrier and untouched tail targets are translated.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $F_t(d,j)=j+d(j\bmod n)$ evaluates a target at a natural cursor slot. $\mathrm{Sweep}(d,k)$ repeats head comparison followed by rotation $k$ times. $\mathrm{Carrier}(F,k)$ is the vector after successive adjacent forward comparisons at positions $0,\ldots,k-1$, carrying the larger target onward.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) , 2 \le  n \to  \forall  (d : I_{n} \to  \mathbb Z), \forall  k < n, \operatorname{Ft} (\operatorname{Sweep} d k) 0 = \operatorname{Carrier} (\operatorname{Ft} d) k k - \operatorname{rep}\,k \land  \forall  (j : \mathbb N), 0 < j \to  j + k < n \to  \operatorname{Ft} (\operatorname{Sweep} d k) j = \operatorname{Ft} d (j + k) - \operatorname{rep}\,k
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/SweepCarrier.lean#L86-L113

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
import Definitions.Def_LX_ForwardCarrier
import Definitions.Def_LX_SweepCarrier

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
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

theorem LX.AffineScan.sweep_prefix_values (hn : 2 ≤ n) (d : Fin n → ℤ) (k : ℕ) (hk : k < n) :
    atTarget (sweep d k) 0 = ForwardCarrier.sweepPrefix (atTarget d) k k - k ∧
    ∀ j : ℕ, 0 < j → j+k < n →
      atTarget (sweep d k) j = atTarget d (j+k) - k := by sorry

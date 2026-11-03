-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_positive_endpoint_length
-- name    : LX.Core.ZeroGap.positive_endpoint_length
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:58:38.551073+00:00
-- url     : https://prove2.me/theorems/c7e568fa-3e67-4075-b37b-618560700f17
-- title:
--   A positive initial displacement reaches across a zero interior gap to its endpoint
-- statement:
--   A positive initial displacement reaches across a zero interior gap to its endpoint.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{Lift}(p,c,d)$ means $\sum_i d(i)=0$ and $i+d(i)\equiv p^{-1}(i)+c\pmod n$ for every residue $i$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (d : I_{n} \to  \mathbb Z), \operatorname{Lift} p 0 d \to  \forall  (v : I_{n}), 0 < d 0 \to  (\forall  (j : I_{n}), 0 < \operatorname{rep}\,j \to  \operatorname{rep}\,j < \operatorname{rep}\,v \to  d j = 0) \to  \operatorname{rep}\,v \le  d 0
--   $$
--
--   This identity can be used while tracking the exact cost or structure of the sorting construction.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapCentered.lean#L30-L45

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
import Definitions.Def_LX_Graph

namespace Int
end Int
namespace LX
end LX
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
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.Core.ZeroGap.positive_endpoint_length {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (v : Fin n) (hpos : 0 < d 0)
    (hgap : ∀ j : Fin n, 0 < j.val → j.val < v.val → d j=0) : (v : ℤ) ≤ d 0 := by sorry

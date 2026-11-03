-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_endpoint_swap_inversions
-- name    : LX.Core.ZeroGap.endpoint_swap_inversions
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:59:25.120586+00:00
-- url     : https://prove2.me/theorems/5874b8df-3385-43dd-b834-ea3667c29e8e
-- title:
--   Swapping across a zero gap reduces affine inversions by exactly twice the gap length minus one
-- statement:
--   Swapping across a zero gap reduces affine inversions by exactly twice the gap length minus one.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $J(F)=\sum_{i<j}|\lfloor(F(j)-F(i))/n\rfloor|$ is affine inversion count. $\mathrm{Sw}(F,v)=F\circ(0\ v)$ swaps the two target entries.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (F : I_{n} \to  \mathbb Z) (v : I_{n}), 0 < \operatorname{rep}\,v \to  \operatorname{rep}\,v \le  F 0 \to  F v \le  0 \to  F 0 - F v < \operatorname{rep}\,n \to  (\forall  (i : I_{n}), 0 < \operatorname{rep}\,i \to  \operatorname{rep}\,i < \operatorname{rep}\,v \to  F i = \operatorname{rep}\,i) \to  J F = J (\operatorname{Sw} F v) + (2\, \operatorname{rep}\,v - 1)
--   $$
--
--   This identity can be used while tracking the exact cost or structure of the sorting construction.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapInversionSum.lean#L44-L80

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
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_ZeroGapInversionTerms

namespace Int
end Int
namespace LX
end LX
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

theorem LX.Core.ZeroGap.endpoint_swap_inversions (F : Fin n → ℤ) (v : Fin n) (hv : 0 < v.val)
    (hA : (v : ℤ) ≤ F 0) (hB : F v ≤ 0) (hspan : F 0-F v < (n : ℤ))
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < v.val → F i=(i : ℤ)) :
    LiftedModel.inversionCount F=LiftedModel.inversionCount (swapEndpoints F v)+(2*v.val-1) := by sorry

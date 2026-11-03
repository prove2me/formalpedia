-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_other_row_terms
-- name    : LX.Core.ZeroGap.other_row_terms
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:59:10.000135+00:00
-- url     : https://prove2.me/theorems/c973d9db-b95b-4b70-84a5-689156da98a9
-- title:
--   Every nonendpoint inversion row changes only at its interior-to-endpoint contribution
-- statement:
--   Every nonendpoint inversion row changes only at its interior-to-endpoint contribution.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{Sw}(F,v)=F\circ(0\ v)$ swaps the two target entries. $j(F,i,j)=|\lfloor(F(j)-F(i))/n\rfloor|$ for $i<j$, and is zero otherwise.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (F : I_{n} \to  \mathbb Z) (v i j : I_{n}), i \ne  0 \to  i \ne  v \to  \operatorname{rep}\,v \le  F 0 \to  F v \le  0 \to  F 0 - F v < \operatorname{rep}\,n \to  (\forall  (k : I_{n}), 0 < \operatorname{rep}\,k \to  \operatorname{rep}\,k < \operatorname{rep}\,v \to  F k = \operatorname{rep}\,k) \to  j F i j = j (\operatorname{Sw} F v) i j + \text{if} 0 < \operatorname{rep}\,i \land  \operatorname{rep}\,i < \operatorname{rep}\,v \text{then} \text{if} j = v \text{then} 1 \text{else} 0 \text{else} 0
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapInversionRows.lean#L43-L67

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
import Definitions.Def_LX_ZeroGapInversionTerms

namespace Int
end Int
namespace LX
end LX
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

theorem LX.Core.ZeroGap.other_row_terms (F : Fin n → ℤ) (v i j : Fin n)
    (hi0 : i ≠ 0) (hiv : i ≠ v)
    (hA : (v : ℤ) ≤ F 0) (hB : F v ≤ 0) (hspan : F 0-F v < (n : ℤ))
    (hgap : ∀ k : Fin n, 0 < k.val → k.val < v.val → F k=(k : ℤ)) :
    inversionTerm F i j=inversionTerm (swapEndpoints F v) i j+
      if 0 < i.val ∧ i.val < v.val then (if j=v then 1 else 0) else 0 := by sorry

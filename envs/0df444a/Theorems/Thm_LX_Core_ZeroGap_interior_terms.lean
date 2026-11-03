-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_interior_terms
-- name    : LX.Core.ZeroGap.interior_terms
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:59:07.02166+00:00
-- url     : https://prove2.me/theorems/05cfee31-6c33-4f1f-9139-e9c9ca0dd729
-- title:
--   Each interior gap coordinate contributes two inversions before the endpoint swap and none afterward
-- statement:
--   Each interior gap coordinate contributes two inversions before the endpoint swap and none afterward.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{Sw}(F,v)=F\circ(0\ v)$ swaps the two target entries. $j(F,i,j)=|\lfloor(F(j)-F(i))/n\rfloor|$ for $i<j$, and is zero otherwise.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (F : I_{n} \to  \mathbb Z) (v j : I_{n}), 0 < \operatorname{rep}\,j \to  \operatorname{rep}\,j < \operatorname{rep}\,v \to  \operatorname{rep}\,v \le  F 0 \to  F v \le  0 \to  F 0 - F v < \operatorname{rep}\,n \to  F j = \operatorname{rep}\,j \to  j F 0 j = 1 \land  j F j v = 1 \land  j (\operatorname{Sw} F v) 0 j = 0 \land  j (\operatorname{Sw} F v) j v = 0
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapInversionTerms.lean#L32-L50

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

theorem LX.Core.ZeroGap.interior_terms (F : Fin n → ℤ) (v j : Fin n)
    (hj0 : 0 < j.val) (hjv : j.val < v.val)
    (hA : (v : ℤ) ≤ F 0) (hB : F v ≤ 0) (hspan : F 0-F v < (n : ℤ)) (hF : F j=(j : ℤ)) :
    inversionTerm F 0 j=1 ∧ inversionTerm F j v=1 ∧
      inversionTerm (swapEndpoints F v) 0 j=0 ∧ inversionTerm (swapEndpoints F v) j v=0 := by sorry

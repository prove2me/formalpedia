-- Prove2me | Theorems.Thm_LX_Core_WordReflection_mirror_letter_eval
-- name    : LX.Core.WordReflection.mirror_letter_eval
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:26:57.007889+00:00
-- url     : https://prove2.me/theorems/0bf673ea-06ff-4a9a-aab1-e30474daa915
-- title:
--   Conjugation by the standard reflection evaluates each inverse generator
-- statement:
--   Conjugation by the standard reflection evaluates each inverse generator.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\sigma(i)=1-i$ is the standard cyclic reflection. The symmetric alphabet $\mathcal A_{\pm}$ contains forward rotation, inverse rotation and adjacent exchange; inverse letters reverse the two rotation letters and fix exchange.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (a : \mathcal A_{\pm}), a_{\rm inverse,ev} = \sigma\, a_{\rm ev}\, \sigma
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/WordReflection.lean#L27-L49

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordReflection

namespace LX.Core
end LX.Core
namespace LX.Core.WordReflection
end LX.Core.WordReflection

namespace LX.Core.WordReflection
end LX.Core.WordReflection
open LX
open LX.Core
open LX.Core.WordReflection
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.Core.WordReflection.mirror_letter_eval (a : Letter) :
    a.inverse.eval (n := n)=reflection*a.eval*reflection := by sorry

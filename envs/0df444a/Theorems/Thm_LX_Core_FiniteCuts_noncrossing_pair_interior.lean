-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_noncrossing_pair_interior
-- name    : LX.Core.FiniteCuts.noncrossing_pair_interior
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:02:47.77882+00:00
-- url     : https://prove2.me/theorems/46491a8b-6671-4162-98ef-eeea1459fd14
-- title:
--   The interior of a noncrossing involutive pair is invariant under the matching
-- statement:
--   The interior of a noncrossing involutive pair is invariant under the matching.
--
--   Let $n$ be a natural number and let $I_n=\{0,\ldots,n-1\}$; this set may be empty. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{NC}(p)$ excludes $a<b<c<d$ with $p(a)=c$ and $p(b)=d$. Involution means $p^2=1$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N) (p : \mathfrak S(I_n)), \operatorname{Invol} p \to  \operatorname{NC} p \to  \forall  (a b x : I_{n}), \operatorname{rep}\,a < \operatorname{rep}\,x \to  \operatorname{rep}\,x < \operatorname{rep}\,b \to  p a = b \to  \operatorname{rep}\,a < \operatorname{rep}\,(p x) \land  \operatorname{rep}\,(p x) < \operatorname{rep}\,b
--   $$
--
--   This supplies a local geometric constraint for the subsequent cycle and matching arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LinearMatchingGeometry.lean#L28-L53

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
import Definitions.Def_LX_LinearMatchingGeometry

namespace LX.Core
end LX.Core
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
variable {n : ℕ}

theorem LX.Core.FiniteCuts.noncrossing_pair_interior (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (a b x : Fin n)
    (hax : a.val < x.val) (hxb : x.val < b.val) (hab : p a=b) :
    a.val < (p x).val ∧ (p x).val < b.val := by sorry

-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_nested_pair_exterior
-- name    : LX.Core.FiniteCuts.nested_pair_exterior
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:03:44.136329+00:00
-- url     : https://prove2.me/theorems/0ee12a39-1908-4c75-8a42-7b444800f834
-- title:
--   In a fully nested fixed-point-free matching, the exterior prefix and suffix are paired with one another
-- statement:
--   In a fully nested fixed-point-free matching, the exterior prefix and suffix are paired with one another.
--
--   Let $n$ be a natural number and let $I_n=\{0,\ldots,n-1\}$; this set may be empty. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{NC}(p)$ excludes $a<b<c<d$ with $p(a)=c$ and $p(b)=d$. $\mathrm{NS}(p)$ excludes $a<b<c<d$ with $p(a)=b$ and $p(c)=d$. Involution means $p^2=1$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N) (p : \mathfrak S(I_n)), \operatorname{Invol} p \to  \operatorname{NC} p \to  \operatorname{NS} p \to  (\forall  (i : I_{n}), p i \ne  i) \to  \forall  (a b : I_{n}), \operatorname{rep}\,a < \operatorname{rep}\,b \to  p a = b \to  \forall  (x : I_{n}), (\operatorname{rep}\,x < \operatorname{rep}\,a \to  \operatorname{rep}\,b < \operatorname{rep}\,(p x)) \land  (\operatorname{rep}\,b < \operatorname{rep}\,x \to  \operatorname{rep}\,(p x) < \operatorname{rep}\,a)
--   $$
--
--   This supplies a local geometric constraint for the subsequent cycle and matching arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/NestedMatchingGeometry.lean#L25-L69

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
import Definitions.Def_LX_NestedMatchingGeometry

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

theorem LX.Core.FiniteCuts.nested_pair_exterior (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (hsep : NoSeparatedPairs p) (hfixed : ∀ i, p i ≠ i)
    (a b : Fin n) (hab : a.val < b.val) (hpab : p a=b) (x : Fin n) :
    (x.val < a.val → b.val < (p x).val) ∧
      (b.val < x.val → (p x).val < a.val) := by sorry

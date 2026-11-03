-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_two_fixed_matching_reflection
-- name    : LX.Core.FiniteCuts.two_fixed_matching_reflection
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:03:13.683606+00:00
-- url     : https://prove2.me/theorems/67b5bb17-7eac-4472-9d02-e003d37ca809
-- title:
--   A two-fixed noncrossing matching without adjacent pairs is reflection away from zero
-- statement:
--   A two-fixed noncrossing matching without adjacent pairs is reflection away from zero.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{NC}(p)$ excludes $a<b<c<d$ with $p(a)=c$ and $p(b)=d$. Involution means $p^2=1$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)), \operatorname{Invol} p \to  \operatorname{NC} p \to  \forall  (t : I_{n}), 0 < \operatorname{rep}\,t \to  (\forall  (i : I_{n}), p i = i \Longleftrightarrow  i = 0 \lor  i = t) \to  (\forall  (i : I_{n}), \operatorname{rep}\,i + 1 \ne  \operatorname{rep}\,(p i)) \to  \forall  (i : I_{n}), i \ne  0 \to  \operatorname{rep}\,i + \operatorname{rep}\,(p i) = n
--   $$
--
--   This supplies a local geometric constraint for the subsequent cycle and matching arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/TwoFixedMatchingReflection.lean#L82-L103

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
variable {n : ℕ} [NeZero n]

theorem LX.Core.FiniteCuts.two_fixed_matching_reflection (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (t : Fin n) (ht : 0<t.val)
    (hfixed : ∀ i, p i=i ↔ i=0 ∨ i=t)
    (hnoadj : ∀ i : Fin n, i.val+1 ≠ (p i).val) :
    ∀ i : Fin n, i ≠ 0 → i.val+(p i).val=n := by sorry

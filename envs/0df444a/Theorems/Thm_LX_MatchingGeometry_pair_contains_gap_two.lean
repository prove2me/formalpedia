-- Prove2me | Theorems.Thm_LX_MatchingGeometry_pair_contains_gap_two
-- name    : LX.MatchingGeometry.pair_contains_gap_two
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:23:31.065192+00:00
-- url     : https://prove2.me/theorems/2707a89f-b869-440c-9c1d-fb5adbe589f2
-- title:
--   A noncrossing pair interval contains a pair at linear distance two under the stated local exclusions
-- statement:
--   A noncrossing pair interval contains a pair at linear distance two under the stated local exclusions.
--
--   Let $n$ be a natural number and let $I_n=\{0,\ldots,n-1\}$; this set may be empty. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{NC}(p)$ excludes $a<b<c<d$ with $p(a)=c$ and $p(b)=d$. Involution means $p^2=1$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N) (q : \mathfrak S(I_n)), \operatorname{Invol} q \to  \operatorname{NC} q \to  (\forall  (i : I_{n}), \operatorname{rep}\,i + 1 \ne  \operatorname{rep}\,(q i)) \to  (\forall  (i j : I_{n}), \operatorname{rep}\,i + 1 = \operatorname{rep}\,j \to  q i = i \to  q j \ne  j) \to  \forall  (a b : I_{n}), \operatorname{rep}\,a < \operatorname{rep}\,b \to  q a = b \to  \exists  x y, \operatorname{rep}\,a \le  \operatorname{rep}\,x \land  \operatorname{rep}\,y \le  \operatorname{rep}\,b \land  \operatorname{rep}\,x + 2 = \operatorname{rep}\,y \land  q x = y
--   $$
--
--   This supplies a local geometric constraint for the subsequent cycle and matching arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/MatchingFixedNeighbors.lean#L9-L40

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
import Definitions.Def_LX_LinearMatchingGeometry
import Definitions.Def_LX_WordMetric

namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.MatchingGeometry
end LX.MatchingGeometry

namespace LX.MatchingGeometry
end LX.MatchingGeometry
open LX
open LX.MatchingGeometry
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}

theorem LX.MatchingGeometry.pair_contains_gap_two (q : State n) (hinv : Function.Involutive q)
    (hnc : LX.Core.FiniteCuts.NoncrossingPairs q)
    (hnoadj : ∀ i : Fin n,i.val+1 ≠ (q i).val)
    (hnofix : ∀ i j : Fin n,i.val+1=j.val → q i=i → q j ≠ j)
    (a b : Fin n) (hab : a.val < b.val) (he : q a=b) :
    ∃ x y : Fin n,a.val ≤ x.val ∧ y.val ≤ b.val ∧ x.val+2=y.val ∧ q x=y := by sorry

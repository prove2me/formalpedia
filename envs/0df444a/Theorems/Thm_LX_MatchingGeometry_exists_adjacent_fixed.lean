-- Prove2me | Theorems.Thm_LX_MatchingGeometry_exists_adjacent_fixed
-- name    : LX.MatchingGeometry.exists_adjacent_fixed
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:23:57.293643+00:00
-- url     : https://prove2.me/theorems/1002d250-2522-44e6-95bd-961b1499db5a
-- title:
--   A sufficiently large noncrossing involution has adjacent cyclic fixed points when adjacent pairs are excluded and distance-two pairs are unique
-- statement:
--   A sufficiently large noncrossing involution has adjacent cyclic fixed points when adjacent pairs are excluded and distance-two pairs are unique.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{NC}(p)$ excludes $a<b<c<d$ with $p(a)=c$ and $p(b)=d$. $\operatorname{supp}(p)$ is the moved-point set and $\operatorname{cycles}(p)$ its nontrivial disjoint cycle factors; cycle membership includes fixed singleton orbits. Involution means $p^2=1$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (q : \mathfrak S(I_n)), \operatorname{Invol} q \to  \operatorname{NC} q \to  4 \le  (\operatorname{supp} q)_{\#} \to  (\forall  (i : I_{n}), q i \ne  i + 1) \to  (\forall  (i j : I_{n}), q i = i + 2 \to  q j = j + 2 \to  i = j) \to  \exists  i, q i = i \land  q (i + 1) = i + 1
--   $$
--
--   This supplies a local geometric constraint for the subsequent cycle and matching arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/MatchingFixedNeighbors.lean#L71-L212

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
variable [NeZero n]

theorem LX.MatchingGeometry.exists_adjacent_fixed (q : State n) (hinv : Function.Involutive q)
    (hnc : LX.Core.FiniteCuts.NoncrossingPairs q) (hsize : 4 ≤ q.support.card)
    (hnoadj : ∀ i : Fin n,q i ≠ i+1)
    (hunique : ∀ i j : Fin n,q i=i+2 → q j=j+2 → i=j) :
    ∃ i : Fin n,q i=i ∧ q (i+1)=i+1 := by sorry

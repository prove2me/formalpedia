-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_sole_zero_fixed_matching_reflection
-- name    : LX.Core.FiniteCuts.sole_zero_fixed_matching_reflection
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:04:04.574003+00:00
-- url     : https://prove2.me/theorems/7c8b7c31-ee7f-4c6f-9009-07b22f6fb0e0
-- title:
--   A noncrossing involution fixing only zero with a unique adjacent pair reflects the remaining interval
-- statement:
--   A noncrossing involution fixing only zero with a unique adjacent pair reflects the remaining interval.
--
--   Let $n$ be a natural number and let $I_n=\{0,\ldots,n-1\}$; this set may be empty. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{NC}(p)$ excludes $a<b<c<d$ with $p(a)=c$ and $p(b)=d$. Involution means $p^2=1$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N) (p : \mathfrak S (n + 1)), \operatorname{Invol} p \to  \operatorname{NC} p \to  p 0 = 0 \to  (\forall  (i : I_{n + 1}), p i = i \to  i = 0) \to  (\forall  (a b : I_{n + 1}), \operatorname{rep}\,a + 1 = \operatorname{rep}\,(p a) \to  \operatorname{rep}\,b + 1 = \operatorname{rep}\,(p b) \to  a = b) \to  \forall  (i : I_{n + 1}), i \ne  0 \to  \operatorname{rep}\,i + \operatorname{rep}\,(p i) = n + 1
--   $$
--
--   This supplies a local geometric constraint for the subsequent cycle and matching arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/WindowMatchingReflection.lean#L48-L80

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

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace List
end List

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
variable {n b : ℕ}

theorem LX.Core.FiniteCuts.sole_zero_fixed_matching_reflection (p : State (n+1))
    (hinv : Function.Involutive p) (hnc : NoncrossingPairs p) (hzero : p 0=0)
    (hfixed : ∀ i : Fin (n+1), p i=i → i=0)
    (hunique : ∀ a b : Fin (n+1), a.val+1=(p a).val → b.val+1=(p b).val → a=b) :
    ∀ i : Fin (n+1), i ≠ 0 → i.val+(p i).val=n+1 := by sorry

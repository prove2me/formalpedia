-- Prove2me | Theorems.Thm_LX_AnchoredPhases_odd_zero_reserve_exception_seven
-- name    : LX.AnchoredPhases.odd_zero_reserve_exception_seven
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:23:58.075975+00:00
-- url     : https://prove2.me/theorems/44d1d0fe-d5bc-402d-a085-31a69a486f46
-- title:
--   The two seven-position exceptional reflection neighbors have sorting words of length at most twenty-five
-- statement:
--   The two seven-position exceptional reflection neighbors have sorting words of length at most twenty-five.
--
--   Work on $I_7=\mathbb Z/7\mathbb Z$, represented by $0,\ldots,6$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. An existential $w$ is a finite word in these generators. Natural subtraction is truncated at zero; scalar price expressions and quantities coerced by $\operatorname{rep}$ are read in the integers. The identity permutation is $1$. Words use forward rotation $l:i\mapsto i+1$ and adjacent exchange $x=(0\ 1)$; $\operatorname{ev}(w)$ is their ordered product.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (p : \mathfrak S(I_7)) (r u : I_{7}), (\forall  (i : I_{7}), (p\, \operatorname{swap} u (u + 1)) i = r - i) \to  \operatorname{rep}\,r = 3 \land  \operatorname{rep}\,u = 4 \lor  \operatorname{rep}\,r = 4 \land  \operatorname{rep}\,u = 1 \to  \exists  w, p\, \operatorname{ev} w = 1 \land  w_{\ell} \le  25
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/OddZeroReserveSeven.lean#L8-L28

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
import Definitions.Def_LX_WordMetric

namespace LX
end LX
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem LX.AnchoredPhases.odd_zero_reserve_exception_seven (p : State 7) (r u : Fin 7)
    (hp : ∀ i,(p*Equiv.swap u (u+1)) i=r-i)
    (hcase : (r.val=3 ∧ u.val=4) ∨ (r.val=4 ∧ u.val=1)) :
    ∃ w : List Letter,p*eval w=1 ∧ w.length ≤ 25 := by sorry

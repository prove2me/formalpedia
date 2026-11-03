-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_shifted_unique_adjacent_of_inherited_extremes
-- name    : LX.Core.FiniteCuts.shifted_unique_adjacent_of_inherited_extremes
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:03:34.958009+00:00
-- url     : https://prove2.me/theorems/9ff59645-adaf-41d2-a69d-4393ae3ef4e2
-- title:
--   Inherited majorized extreme coordinates make a shifted matching's adjacent pair unique in odd width
-- statement:
--   Inherited majorized extreme coordinates make a shifted matching's adjacent pair unique in odd width.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{Lift}(p,c,d)$ means $\sum_i d(i)=0$ and $i+d(i)\equiv p^{-1}(i)+c\pmod n$ for every residue $i$. $\mathrm{Maj}(d)$ means $2\sum_{i\in S}d(i)\le |S|(n-|S|)$ for every subset $S\subseteq I_n$. $\mathrm{Shift}(p,c,h)(i)=p^{-1}(i)+c+h$ modulo $n$. Involution means $p^2=1$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (c : \mathbb Z) (original d : I_{n} \to  \mathbb Z), \operatorname{Maj} original \to  \operatorname{Lift} p c d \to  \forall  (h : \mathbb Z), \operatorname{rep}\,n = 2\, h + 1 \to  (\forall  (i : I_{n}), 0 \le  d i + h \land  d i + h < \operatorname{rep}\,n) \to  (\forall  (i : I_{n}), d i = h \to  original i = h) \to  \operatorname{Invol} (\operatorname{Shift} p c h) \to  \forall  (a b : I_{n}), \operatorname{rep}\,a + 1 = \operatorname{rep}\,((\operatorname{Shift} p c h) a) \to  \operatorname{rep}\,b + 1 = \operatorname{rep}\,((\operatorname{Shift} p c h) b) \to  a = b
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ShiftedAdjacentPairs.lean#L41-L60

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
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_Graph
import Definitions.Def_LX_StrictBandInversionCapacity

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteGaps
end LX.Core.FiniteGaps
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem LX.Core.FiniteCuts.shifted_unique_adjacent_of_inherited_extremes {p : State n} {c : ℤ}
    {original d : Fin n → ℤ} (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p c d) (h : ℤ) (hn : (n : ℤ)=2*h+1)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ))
    (hinherit : ∀ i, d i=h → original i=h)
    (hinv : Function.Involutive (shiftedLiftPermutation p c h)) :
    ∀ a b : Fin n, a.val+1=(shiftedLiftPermutation p c h a).val →
      b.val+1=(shiftedLiftPermutation p c h b).val → a=b := by sorry

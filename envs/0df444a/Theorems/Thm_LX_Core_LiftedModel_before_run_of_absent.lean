-- Prove2me | Theorems.Thm_LX_Core_LiftedModel_before_run_of_absent
-- name    : LX.Core.LiftedModel.before_run_of_absent
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:11.185845+00:00
-- url     : https://prove2.me/theorems/01f40051-7eed-4651-9303-1aaab97585aa
-- title:
--   A valid pair absent from all recorded events retains its lifted order after the whole word
-- statement:
--   A valid pair absent from all recorded events retains its lifted order after the whole word.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. Variables named events or part denote event lists; untyped vertex variables range over $I_n$. Pairwise separation refers to earlier and later entries in their list order. A lifted configuration additionally records an integer position for each token and an integer cursor. A pair key consists of two ordered token labels and an integer period shift. Alignment means that cursor and token positions reduce to the physical cursor and physical token locations modulo $n$. The lifted run iterates these steps in word order. The event list records these normalized pair keys at exchange letters, retaining execution order. The symmetric alphabet $\mathcal A_{\pm}$ contains forward rotation, inverse rotation and adjacent exchange; inverse letters reverse the two rotation letters and fix exchange. A valid key has increasing token labels and shift divisible by $n$; its before relation compares the first lifted position with the second plus that shift.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) , 2 \le  n \to  \forall  (w : \operatorname{Seq} \mathcal A_{\pm}) (s : \operatorname{Conf} n), \operatorname{Aligned} s \to  \forall  (key : \operatorname{Pair} n), key_{\rm valid} \to  key \notin  \operatorname{Events} w s \to  (key_{\rm before} (\operatorname{LRun} w s) \Longleftrightarrow  key_{\rm before} s)
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/TraceInversions.lean#L10-L29

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
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace List
end List

namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
open LX
open LX.Core
open LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]

theorem LX.Core.LiftedModel.before_run_of_absent (hn : 2 ≤ n) (w : List Letter) {s : Configuration n}
    (hs : Aligned s) (key : PairKey n) (hk : key.Valid)
    (habsent : key ∉ events w s) : key.Before (run w s) ↔ key.Before s := by sorry

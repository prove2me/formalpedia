-- Prove2me | Theorems.Thm_LX_Core_LiftedModel_x_changes_only_event
-- name    : LX.Core.LiftedModel.x_changes_only_event
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:11.062616+00:00
-- url     : https://prove2.me/theorems/904d156b-c3a7-4554-9fbf-14afbc7f4c47
-- title:
--   An exchange changes the order of only its own normalized token-pair event
-- statement:
--   An exchange changes the order of only its own normalized token-pair event.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. A lifted configuration additionally records an integer position for each token and an integer cursor. A pair key consists of two ordered token labels and an integer period shift. Alignment means that cursor and token positions reduce to the physical cursor and physical token locations modulo $n$. The current event key is the normalized pair of tokens at the cursor and its successor, with shift determined by their lifted positions. A lifted step performs the physical update and records the corresponding unit token motions and cursor increment. The symmetric alphabet $\mathcal A_{\pm}$ contains forward rotation, inverse rotation and adjacent exchange; inverse letters reverse the two rotation letters and fix exchange. A valid key has increasing token labels and shift divisible by $n$; its before relation compares the first lifted position with the second plus that shift.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) , 2 \le  n \to  \forall  (s : \operatorname{Conf} n), \operatorname{Aligned} s \to  \forall  (key : \operatorname{Pair} n), key_{\rm valid} \to  \operatorname{Current} s \ne  key \to  (key_{\rm before} (\operatorname{LStep} x s) \Longleftrightarrow  key_{\rm before} s)
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PairOrder.lean#L38-L73

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
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.Core.LiftedModel.x_changes_only_event (hn : 2 ≤ n) {s : Configuration n} (hs : Aligned s)
    (key : PairKey n) (hk : key.Valid) (hne : eventKey s ≠ key) :
    key.Before (step .x s) ↔ key.Before s := by sorry

-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_event_path_straddles
-- name    : LX.Core.ZeroGap.event_path_straddles
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:20:16.525127+00:00
-- url     : https://prove2.me/theorems/8d9cdb60-321d-41aa-a8ba-a890f286d1c6
-- title:
--   A component path crossing a missing vertex contains an event whose interior contains that vertex
-- statement:
--   A component path crossing a missing vertex contains an event whose interior contains that vertex.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. Variables named events or part denote event lists; untyped vertex variables range over $I_n$. Pairwise separation refers to earlier and later entries in their list order. An event $e=(e_1,e_2)$ is an ordered pair of residue positions. $\mathrm{Reach}(L,u,v)$ means connectivity through undirected endpoint edges of the event list $L$, including a path of length zero. $\mathrm{Inside}(e,i)$ means $0<\operatorname{rep}(i-e_1)<\operatorname{rep}(e_2-e_1)$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (events : \operatorname{Seq} (\mathcal E n)), (\forall  e \in  events, \operatorname{rep}\,e_1 < \operatorname{rep}\,e_2) \to  \forall  (a b z : I_{n}), \operatorname{rep}\,a < \operatorname{rep}\,b \to  \neg \operatorname{Reach} events a b \to  \operatorname{Reach} events a z \to  \operatorname{rep}\,b < \operatorname{rep}\,z \to  \exists  e \in  events, \operatorname{Reach} events a e_1 \land  \operatorname{Reach} events a e_2 \land  \operatorname{Inside} e b
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LinearEventComponents.lean#L25-L52

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
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph

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
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.Core.ZeroGap.event_path_straddles (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (a b z : Fin n)
    (ha : a.val < b.val) (havoid : ¬EventReaches events a b)
    (hp : EventReaches events a z) (hz : b.val < z.val) :
    ∃ e ∈ events, EventReaches events a e.1 ∧ EventReaches events a e.2 ∧ Inside e b := by sorry

-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_maximal_event_support_pair
-- name    : LX.Core.ZeroGap.maximal_event_support_pair
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:02:37.938209+00:00
-- url     : https://prove2.me/theorems/eba3fc7c-7527-4236-bdec-9508106ac20b
-- title:
--   Maximal support forces each event to be an isolated transposition in the product
-- statement:
--   Maximal support forces each event to be an isolated transposition in the product.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. Variables named events or part denote event lists; untyped vertex variables range over $I_n$. Pairwise separation refers to earlier and later entries in their list order. An event $e=(e_1,e_2)$ is an ordered pair of residue positions. $\tau(e)$ is the transposition of the two event endpoints; products use the event-list order. $\operatorname{supp}(p)$ is the moved-point set and $\operatorname{cycles}(p)$ its nontrivial disjoint cycle factors; cycle membership includes fixed singleton orbits.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (events : \operatorname{Seq} (\mathcal E n)), (\operatorname{supp} (\operatorname{map} \tau events)_{\Pi})_{\#} = 2\, events_{\ell} \to  \forall  e \in  events, e_1 \ne  e_2 \land  (\operatorname{map} \tau events)_{\Pi} e_1 = e_2 \land  (\operatorname{map} \tau events)_{\Pi} e_2 = e_1
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/MaximalEventSupport.lean#L44-L62

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
import Definitions.Def_LX_ZeroGapEventGeometry

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
variable {n : ℕ} [NeZero n]

theorem LX.Core.ZeroGap.maximal_event_support_pair (events : List (Event n))
    (hcard : (events.map eventSwap).prod.support.card=2*events.length)
    (e : Event n) (he : e ∈ events) :
    e.1 ≠ e.2 ∧ (events.map eventSwap).prod e.1=e.2 ∧
      (events.map eventSwap).prod e.2=e.1 := by sorry

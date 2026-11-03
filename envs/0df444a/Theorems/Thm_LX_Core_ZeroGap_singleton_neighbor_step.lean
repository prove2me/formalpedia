-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_singleton_neighbor_step
-- name    : LX.Core.ZeroGap.singleton_neighbor_step
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:19:55.77473+00:00
-- url     : https://prove2.me/theorems/a0b244d2-b8b6-4104-98ec-fe57d92756e2
-- title:
--   Attaching a fixed singleton to a minimal event component yields an adjacent arrow avoiding a chosen extreme
-- statement:
--   Attaching a fixed singleton to a minimal event component yields an adjacent arrow avoiding a chosen extreme.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. Variables named events or part denote event lists; untyped vertex variables range over $I_n$. Pairwise separation refers to earlier and later entries in their list order. An event $e=(e_1,e_2)$ is an ordered pair of residue positions. $\tau(e)$ is the transposition of the two event endpoints; products use the event-list order. $\mathrm{Comp}(L,u)$ is the set of vertices reachable from $u$. $\mathrm{Sel}(L,u)$ keeps the events in that component in their original order. $\mathrm{Adj}(S,x,y)$ means distinct vertices of $S$ with no vertex of $S$ strictly between their representatives. $\mathrm{Ext}(S,r)$ means $r$ is a lower or upper extreme of the ordered set $S$. $\mathrm{Safe}(L,u,r)$ asserts an arrow of the event product between rank-adjacent vertices of $\mathrm{Comp}(L,u)$, with both endpoints different from $r$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (events : \operatorname{Seq} (\mathcal E n)) (a b r : I_{n}), (\forall  e \in  events, \operatorname{rep}\,e_1 < \operatorname{rep}\,e_2) \to  (\operatorname{Sel} events a)_{\ell} + 1 = (\operatorname{Comp} events a)_{\#} \to  2 \le  (\operatorname{Comp} events a)_{\#} \to  b \notin  \operatorname{Comp} events a \to  (\operatorname{map} \tau events)_{\Pi} b = b \to  r \in  \operatorname{Comp} events a \to  \operatorname{Adj} (\operatorname{insert} b (\operatorname{Comp} events a)) a b \to  \operatorname{Ext} (\operatorname{insert} b (\operatorname{Comp} events a)) r \to  (3 \le  (\operatorname{Comp} events a)_{\#} \to  \operatorname{Ext} (\operatorname{Comp} events a) a \to  \operatorname{Safe} (\operatorname{Sel} events a) a a) \to  \exists  x y, \operatorname{Adj} (\operatorname{insert} b (\operatorname{Comp} events a)) x y \land  (\operatorname{swap} a b\, (\operatorname{map} \tau events)_{\Pi}) x = y \land  x \ne  r \land  y \ne  r
--   $$
--
--   This supplies a local geometric constraint for the subsequent cycle and matching arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/SingletonNeighborStep.lean#L8-L79

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
import Definitions.Def_LX_ExtremeEventBranch
import Definitions.Def_LX_Graph
import Definitions.Def_LX_ShallowNeighborSplice
import Definitions.Def_LX_TwoMovingNeighborStep
import Definitions.Def_LX_ZeroGapComponentCounting
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
variable {n : ℕ} [NeZero n]

theorem LX.Core.ZeroGap.singleton_neighbor_step (events : List (Event n)) (a b r : Fin n)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val)
    (hmin : (componentEvents events a).length+1=(eventComponent events a).card)
    (hcard : 2 ≤ (eventComponent events a).card)
    (hb : b ∉ eventComponent events a)
    (hfixed : (events.map eventSwap).prod b=b)
    (hr : r ∈ eventComponent events a)
    (hgap : RankAdjacent (insert b (eventComponent events a)) a b)
    (hext : IsExtreme (insert b (eventComponent events a)) r)
    (ih : 3 ≤ (eventComponent events a).card → IsExtreme (eventComponent events a) a →
      NeighborAway (componentEvents events a) a a) :
    ∃ x y, RankAdjacent (insert b (eventComponent events a)) x y ∧
      (Equiv.swap a b*(events.map eventSwap).prod) x=y ∧ x ≠ r ∧ y ≠ r := by sorry

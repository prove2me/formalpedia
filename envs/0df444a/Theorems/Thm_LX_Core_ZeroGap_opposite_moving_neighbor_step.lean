-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_opposite_moving_neighbor_step
-- name    : LX.Core.ZeroGap.opposite_moving_neighbor_step
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:20:18.755673+00:00
-- url     : https://prove2.me/theorems/7b04aa7c-beda-4404-a739-15f2dfa59b49
-- title:
--   The two-moving-branch splice yields an adjacent permutation arrow avoiding the selected extreme
-- statement:
--   The two-moving-branch splice yields an adjacent permutation arrow avoiding the selected extreme.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. Variables named events or part denote event lists; untyped vertex variables range over $I_n$. Pairwise separation refers to earlier and later entries in their list order. An event $e=(e_1,e_2)$ is an ordered pair of residue positions. $\mathrm{Reach}(L,u,v)$ means connectivity through undirected endpoint edges of the event list $L$, including a path of length zero. $\mathrm{Comp}(L,u)$ is the set of vertices reachable from $u$. $\mathrm{Sel}(L,u)$ keeps the events in that component in their original order. $\mathrm{Outside}(e,f)$ means neither endpoint of $f$ is in the clockwise open interior of $e$. $\mathrm{Ext}(S,r)$ means $r$ is a lower or upper extreme of the ordered set $S$. $\mathrm{Safe}(L,u,r)$ asserts an arrow of the event product between rank-adjacent vertices of $\mathrm{Comp}(L,u)$, with both endpoints different from $r$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (e : \mathcal E n) (events : \operatorname{Seq} (\mathcal E n)), (\forall  f \in  e \mathbin{::} events, \operatorname{rep}\,f_1 < \operatorname{rep}\,f_2) \to  \operatorname{Pairwise} \operatorname{Outside} (e \mathbin{::} events) \to  (e \mathbin{::} events)_{\ell} + 1 = (\operatorname{Comp} (e \mathbin{::} events) e_1)_{\#} \to  \forall  (r : I_{n}), (\operatorname{Reach} events e_2 r \to  2 \le  (\operatorname{Comp} events e_1)_{\#}) \to  (\operatorname{Reach} events e_1 r \to  2 \le  (\operatorname{Comp} events e_2)_{\#}) \to  (\forall  b \in  [e_1, e_2], 3 \le  (\operatorname{Comp} events b)_{\#} \to  \operatorname{Ext} (\operatorname{Comp} events b) b \to  \operatorname{Safe} (\operatorname{Sel} events b) b b) \to  r \in  \operatorname{Comp} (e \mathbin{::} events) e_1 \to  \operatorname{Ext} (\operatorname{Comp} (e \mathbin{::} events) e_1) r \to  \operatorname{Safe} (e \mathbin{::} events) e_1 r
--   $$
--
--   This supplies a local geometric constraint for the subsequent cycle and matching arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/TwoMovingNeighborStep.lean#L24-L83

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

theorem LX.Core.ZeroGap.opposite_moving_neighbor_step (e : Event n) (events : List (Event n))
    (hlinear : ∀ f ∈ e::events, f.1.val < f.2.val)
    (hsep : (e::events).Pairwise LaterOutside)
    (hmin : (e::events).length+1=(eventComponent (e::events) e.1).card)
    (r : Fin n)
    (ha : EventReaches events e.2 r → 2 ≤ (eventComponent events e.1).card)
    (hb : EventReaches events e.1 r → 2 ≤ (eventComponent events e.2).card)
    (ih : ∀ b ∈ [e.1,e.2], 3 ≤ (eventComponent events b).card →
      IsExtreme (eventComponent events b) b → NeighborAway (componentEvents events b) b b)
    (hr : r ∈ eventComponent (e::events) e.1)
    (hext : IsExtreme (eventComponent (e::events) e.1) r) :
    NeighborAway (e::events) e.1 r := by sorry

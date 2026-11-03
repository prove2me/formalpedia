-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_adjacent_attachment_boundary
-- name    : LX.Core.ZeroGap.adjacent_attachment_boundary
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:19:44.858906+00:00
-- url     : https://prove2.me/theorems/cb00d05a-f056-4a4d-99e5-8a744ea68876
-- title:
--   An attachment across a gap meets an interval component at an extreme vertex
-- statement:
--   An attachment across a gap meets an interval component at an extreme vertex.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. Variables named events or part denote event lists; untyped vertex variables range over $I_n$. Pairwise separation refers to earlier and later entries in their list order. An event $e=(e_1,e_2)$ is an ordered pair of residue positions. $\mathrm{Reach}(L,u,v)$ means connectivity through undirected endpoint edges of the event list $L$, including a path of length zero. $\mathrm{Outside}(e,f)$ means neither endpoint of $f$ is in the clockwise open interior of $e$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (events : \operatorname{Seq} (\mathcal E n)), (\forall  e \in  events, \operatorname{rep}\,e_1 < \operatorname{rep}\,e_2) \to  \operatorname{Pairwise} \operatorname{Outside} events \to  \forall  (lo hi root a b : I_{n}), \operatorname{Reach} events lo hi \to  (\forall  (i : I_{n}), \operatorname{Reach} events lo i \to  \operatorname{rep}\,lo \le  \operatorname{rep}\,i \land  \operatorname{rep}\,i \le  \operatorname{rep}\,hi) \to  \neg \operatorname{Reach} events lo root \to  \operatorname{rep}\,root < \operatorname{rep}\,lo \lor  \operatorname{rep}\,hi < \operatorname{rep}\,root \to  \operatorname{Reach} events root a \to  \operatorname{Reach} events lo b \to  (\forall  (i : I_{n}), \operatorname{Reach} events lo i \to  \neg (\operatorname{min} \operatorname{rep}\,a \operatorname{rep}\,b < \operatorname{rep}\,i \land  \operatorname{rep}\,i < \operatorname{max} \operatorname{rep}\,a \operatorname{rep}\,b)) \to  b = lo \lor  b = hi
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LinearEventComponents.lean#L93-L124

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

theorem LX.Core.ZeroGap.adjacent_attachment_boundary (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (lo hi root a b : Fin n) (hlohi : EventReaches events lo hi)
    (hbound : ∀ i, EventReaches events lo i → lo.val ≤ i.val ∧ i.val ≤ hi.val)
    (havoid : ¬EventReaches events lo root)
    (hout : root.val < lo.val ∨ hi.val < root.val)
    (hra : EventReaches events root a) (hlob : EventReaches events lo b)
    (hgap : ∀ i, EventReaches events lo i →
      ¬(min a.val b.val < i.val ∧ i.val < max a.val b.val)) : b=lo ∨ b=hi := by sorry

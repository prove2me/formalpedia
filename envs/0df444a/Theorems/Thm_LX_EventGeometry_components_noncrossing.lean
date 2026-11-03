-- Prove2me | Theorems.Thm_LX_EventGeometry_components_noncrossing
-- name    : LX.EventGeometry.components_noncrossing
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:21:03.497867+00:00
-- url     : https://prove2.me/theorems/999411ce-c68c-42a8-9eeb-c7d7f723d883
-- title:
--   Separated linear event components cannot alternate along the line
-- statement:
--   Separated linear event components cannot alternate along the line.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. Variables named events or part denote event lists; untyped vertex variables range over $I_n$. Pairwise separation refers to earlier and later entries in their list order. An event $e=(e_1,e_2)$ is an ordered pair of residue positions. $\mathrm{Reach}(L,u,v)$ means connectivity through undirected endpoint edges of the event list $L$, including a path of length zero. $\mathrm{Outside}(e,f)$ means neither endpoint of $f$ is in the clockwise open interior of $e$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (events : \operatorname{Seq} (\mathcal E n)), (\forall  e \in  events, \operatorname{rep}\,e_1 < \operatorname{rep}\,e_2) \to  \operatorname{Pairwise} \operatorname{Outside} events \to  \forall  (a b c d : I_{n}), \operatorname{rep}\,a < \operatorname{rep}\,b \to  \operatorname{rep}\,b < \operatorname{rep}\,c \to  \operatorname{rep}\,c < \operatorname{rep}\,d \to  \operatorname{Reach} events a c \to  \operatorname{Reach} events b d \to  \operatorname{Reach} events a b
--   $$
--
--   This supplies a local geometric constraint for the subsequent cycle and matching arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroDefectCycleGeometry.lean#L12-L48

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
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
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
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.CycleGeometry
end LX.CycleGeometry
namespace LX.EventGeometry
end LX.EventGeometry
namespace List
end List

namespace LX.EventGeometry
end LX.EventGeometry
open LX
open LX.EventGeometry
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem LX.EventGeometry.components_noncrossing (events : List (Event n))
    (hlinear : ∀ e ∈ events,e.1.val < e.2.val)
    (hsep : events.Pairwise LaterOutside)
    (a b c d : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (hac : EventReaches events a c) (hbd : EventReaches events b d) :
    EventReaches events a b := by sorry

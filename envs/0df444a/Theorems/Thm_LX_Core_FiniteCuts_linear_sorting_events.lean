-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_linear_sorting_events
-- name    : LX.Core.FiniteCuts.linear_sorting_events
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:20:39.855917+00:00
-- url     : https://prove2.me/theorems/288043d9-9317-464a-bc6a-e096ef9dd0c7
-- title:
--   Every permutation admits a linear separated event factorization with an exact length and displacement travel
-- statement:
--   Every permutation admits a linear separated event factorization with an exact length and displacement travel.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. Variables named events or part denote event lists; untyped vertex variables range over $I_n$. Pairwise separation refers to earlier and later entries in their list order. $\tau(e)$ is the transposition of the two event endpoints; products use the event-list order. $\mathrm{Outside}(e,f)$ means neither endpoint of $f$ is in the clockwise open interior of $e$. $\mathrm{Travel}(L,u,v,z)$ means an event-edge path from $u$ to $v$ with total signed weight $z$, where an oriented event has weight $\operatorname{rep}(e_2-e_1)$ and reversal negates it. $\operatorname{inv}(p)=|\{(i,j):i<j,\ p(j)<p(i)\}|$ is the ordinary finite inversion number. $\Delta(p,i)=\operatorname{rep}(p(i))-\operatorname{rep}(i)$ is ordinary integer displacement. $\operatorname{supp}(p)$ is the moved-point set and $\operatorname{cycles}(p)$ its nontrivial disjoint cycle factors; cycle membership includes fixed singleton orbits.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)), \exists  events, (\operatorname{map} \tau events)_{\Pi} = p \land  \operatorname{rep}\,events_{\ell} = \sum_{i} |\Delta (\operatorname{inverse} p) i| - \operatorname{rep}\,(\operatorname{inv} p) \land  (\forall  e \in  events, e_1 \in  \operatorname{supp} p \land  e_2 \in  \operatorname{supp} p) \land  (\forall  e \in  events, \operatorname{rep}\,e_1 < \operatorname{rep}\,e_2) \land  \operatorname{Pairwise} \operatorname{Outside} events \land  \forall  (i : I_{n}), \operatorname{Travel} events i ((\operatorname{inverse} p) i) (\Delta (\operatorname{inverse} p) i)
--   $$
--
--   This identity can be used while tracking the exact cost or structure of the sorting construction.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LinearSortingTrace.lean#L39-L110

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
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventTravel

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
namespace List
end List

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open ZeroGap FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem LX.Core.FiniteCuts.linear_sorting_events (p : State n) :
    ∃ events : List (Event n), (events.map eventSwap).prod=p ∧
      (events.length : ℤ)=(∑ i, |_root_.LX.Core.FiniteCuts.displacement p.symm i|)-(inversionNumber p : ℤ) ∧
      (∀ e ∈ events, e.1 ∈ p.support ∧ e.2 ∈ p.support) ∧
      (∀ e ∈ events, e.1.val < e.2.val) ∧ events.Pairwise LaterOutside ∧
      (∀ i, Travel events i (p.symm i) (_root_.LX.Core.FiniteCuts.displacement p.symm i)) := by sorry

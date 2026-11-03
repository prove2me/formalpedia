-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_SortingTrace_events
-- name    : LX.Core.ZeroGap.SortingTrace.events
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:59:01.065242+00:00
-- url     : https://prove2.me/theorems/bce53461-73b4-4175-aac0-3d9ea2eab287
-- title:
--   A short zero-gap sorting trace yields a separated event factorization with signed token travel
-- statement:
--   A short zero-gap sorting trace yields a separated event factorization with signed token travel.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. Variables named events or part denote event lists; untyped vertex variables range over $I_n$. Pairwise separation refers to earlier and later entries in their list order. $\mathrm{Lift}(p,c,d)$ means $\sum_i d(i)=0$ and $i+d(i)\equiv p^{-1}(i)+c\pmod n$ for every residue $i$. $\tau(e)$ is the transposition of the two event endpoints; products use the event-list order. $\mathrm{Outside}(e,f)$ means neither endpoint of $f$ is in the clockwise open interior of $e$. $\mathrm{Travel}(L,u,v,z)$ means an event-edge path from $u$ to $v$ with total signed weight $z$, where an oriented event has weight $\operatorname{rep}(e_2-e_1)$ and reversal negates it. $\mathrm{Sort}(p,d,M)$ records $M$ zero-gap endpoint exchanges, permitting recentering at each step and ending at zero displacement. $\delta(u,v)=\operatorname{rep}(v-u)$ is clockwise distance.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (d : I_{n} \to  \mathbb Z) (M : \mathbb N), \operatorname{Sort} p d M \to  \operatorname{Lift} p 0 d \to  (\forall  (i : I_{n}), 2\, |d i| < \operatorname{rep}\,n) \to  \exists  events, (\operatorname{map} \tau events)_{\Pi} = p \land  events_{\ell} = M \land  (\forall  e \in  events, e_1 \ne  e_2) \land  (\forall  e \in  events, d e_1 \ne  0 \land  d e_2 \ne  0) \land  \operatorname{Pairwise} \operatorname{Outside} events \land  (\forall  e \in  events, 2\, \delta e_1 e_2 < n) \land  \forall  (i : I_{n}), \operatorname{Travel} events i ((\operatorname{inverse} p) i) (d i)
--   $$
--
--   This identity can be used while tracking the exact cost or structure of the sorting construction.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapEvents.lean#L12-L109

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
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventTravel
import Definitions.Def_LX_ZeroGapPair
import Definitions.Def_LX_ZeroGapSorting

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

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.Core.ZeroGap.SortingTrace.events {p : State n} {d : Fin n → ℤ} {M : ℕ}
    (ht : SortingTrace p d M) (hd : AffineLift.IsLift p 0 d)
    (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    ∃ events : List (Event n), (events.map eventSwap).prod=p ∧ events.length=M ∧
      (∀ e ∈ events, e.1 ≠ e.2) ∧ (∀ e ∈ events, d e.1 ≠ 0 ∧ d e.2 ≠ 0) ∧
      events.Pairwise LaterOutside ∧ (∀ e ∈ events, 2*distance e.1 e.2 < n) ∧
      (∀ i, Travel events i (p.symm i) (d i)) := by sorry

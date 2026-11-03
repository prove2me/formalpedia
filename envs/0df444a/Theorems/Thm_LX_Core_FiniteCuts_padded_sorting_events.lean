-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_padded_sorting_events
-- name    : LX.Core.FiniteCuts.padded_sorting_events
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:59:55.802646+00:00
-- url     : https://prove2.me/theorems/7771725d-d95f-42e2-b7b7-85a33c6eb53d
-- title:
--   Padding a finite permutation yields a separated, linearly oriented event factorization with exact length
-- statement:
--   Padding a finite permutation yields a separated, linearly oriented event factorization with exact length.
--
--   Let $n$ be a natural number and let $I_n=\{0,\ldots,n-1\}$; this set may be empty. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. Variables named events or part denote event lists; untyped vertex variables range over $I_n$. Pairwise separation refers to earlier and later entries in their list order. $\tau(e)$ is the transposition of the two event endpoints; products use the event-list order. $\mathrm{Outside}(e,f)$ means neither endpoint of $f$ is in the clockwise open interior of $e$. $\operatorname{inv}(p)=|\{(i,j):i<j,\ p(j)<p(i)\}|$ is the ordinary finite inversion number. $\Delta(p,i)=\operatorname{rep}(p(i))-\operatorname{rep}(i)$ is ordinary integer displacement. $\mathrm{Pad}(W,p)$ acts as $p$ inside the embedded window and fixes its complement. $\operatorname{supp}(p)$ is the moved-point set and $\operatorname{cycles}(p)$ its nontrivial disjoint cycle factors; cycle membership includes fixed singleton orbits.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N) (p : \mathfrak S(I_n)), \text{put }W := \operatorname{initialWindow}_{2n+1,n}; \text{put }q := \operatorname{Pad} W p; \exists  events, (\operatorname{map} \tau events)_{\Pi} = q \land  \operatorname{rep}\,events_{\ell} = \sum_{i} |\Delta p i| - \operatorname{rep}\,(\operatorname{inv} p) \land  (\forall  e \in  events, e_1 \ne  e_2) \land  (\forall  e \in  events, e_1 \in  \operatorname{supp} q \land  e_2 \in  \operatorname{supp} q) \land  (\forall  e \in  events, \operatorname{rep}\,e_1 < \operatorname{rep}\,e_2) \land  \operatorname{Pairwise} \operatorname{Outside} events
--   $$
--
--   This identity can be used while tracking the exact cost or structure of the sorting construction.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PaddedSortingEvents.lean#L11-L80

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
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
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
open scoped BigOperators
variable {n : ℕ}

theorem LX.Core.FiniteCuts.padded_sorting_events (p : State n) :
    let W : FiniteWindow.Window (2*n+1) n := ⟨0,by omega⟩
    let q := FiniteWindow.permutation W p
    ∃ events : List (ZeroGap.Event (2*n+1)),
      (events.map ZeroGap.eventSwap).prod=q ∧
      (events.length : ℤ)=(∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|)-(inversionNumber p : ℤ) ∧
      (∀ e ∈ events, e.1 ≠ e.2) ∧
      (∀ e ∈ events, e.1 ∈ q.support ∧ e.2 ∈ q.support) ∧
      (∀ e ∈ events, e.1.val < e.2.val) ∧ events.Pairwise ZeroGap.LaterOutside := by sorry

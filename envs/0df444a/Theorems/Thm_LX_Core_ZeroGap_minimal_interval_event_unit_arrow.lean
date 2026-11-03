-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_minimal_interval_event_unit_arrow
-- name    : LX.Core.ZeroGap.minimal_interval_event_unit_arrow
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:20:34.725407+00:00
-- url     : https://prove2.me/theorems/67e2ffbe-6102-451e-9396-e653dffa4e96
-- title:
--   A minimal separated interval factorization has a unit arrow
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. An event list $E$ consists of pairs $(x,y)\in I_n^2$, regarded as undirected graph edges. Let $C_E(r)$ be the graph component of $r$, $E_r$ the subsequence of events in that component, $E_{\rm out}(r)$ its complementary subsequence, and $\pi_E$ the ordered product of the corresponding transpositions. Assume each edge is oriented increasingly, and every later event has both endpoints outside the open interval between the endpoints of every earlier event. Let $n>0$, suppose $\pi_E=p$, all event endpoints belong to its nonempty interval support, and $|E|+k(p^{-1})=|\operatorname{supp}(p)|$, where $k$ counts nontrivial cycles. Then
--
--   $$
--   \exists i:\quad|p(i)-i|=1.
--   $$
--
--   A minimal event factorization on an interval cannot avoid every ordinary neighboring arrow.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/InnermostEventComponent.lean#L72-L95

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_ShallowNeighborSplice
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
variable {n : ℕ} [NeZero n]

theorem LX.Core.ZeroGap.minimal_interval_event_unit_arrow (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p)
    (hactive : ∀ e ∈ events, e.1 ∈ p.support ∧ e.2 ∈ p.support)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (hne : p.support.Nonempty) (hinterval : CarrierInterval p.support Finset.univ)
    (hminimal : events.length+(p⁻¹).cycleFactorsFinset.card=p.support.card) :
    ∃ i : Fin n, |_root_.LX.Core.FiniteCuts.displacement p i|=1 := by sorry

-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_opposite_branch_interval
-- name    : LX.Core.ZeroGap.opposite_branch_interval
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:20:15.571539+00:00
-- url     : https://prove2.me/theorems/b0483d79-6d0e-463a-86f8-01e6a2ca2c08
-- title:
--   The opposite event branch is an interval and has an extreme attachment
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. An event list $E$ consists of pairs $(x,y)\in I_n^2$, regarded as undirected graph edges. Let $C_E(r)$ be the graph component of $r$, $E_r$ the subsequence of events in that component, $E_{\rm out}(r)$ its complementary subsequence, and $\pi_E$ the ordered product of the corresponding transpositions. Assume each edge is oriented increasingly, and every later event has both endpoints outside the open interval between the endpoints of every earlier event. Two vertices are rank adjacent in a set if they are distinct members with no member strictly between them in the linear order. An extreme vertex is at or beyond one end of the set. Let $n>0$, let $a,b,r\in I_n$ and $S\subseteq I_n$. Suppose $a,b$ are disconnected, $r\in C_E(a)$, $C_E(b)\subseteq S$, every member of $S$ lies in $C_E(a)\cup C_E(b)$, $r$ is extreme in $S$, and $a,b$ are rank adjacent in $S$. Then
--
--   $$
--   C_E(b)\text{ is an interval relative to }S,\qquad b\text{ is extreme in }C_E(b).
--   $$
--
--   An interval relative to $S$ contains every member of $S$ between any two of its members. This controls how disjoint branches can be joined.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ExtremeEventBranch.lean#L16-L72

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
import Definitions.Def_LX_ShallowNeighborSplice
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

theorem LX.Core.ZeroGap.opposite_branch_interval (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (S : Finset (Fin n)) (a b r : Fin n)
    (hab : ¬EventReaches events a b) (har : EventReaches events a r)
    (hsub : eventComponent events b ⊆ S)
    (hcover : ∀ i ∈ S, EventReaches events a i ∨ EventReaches events b i)
    (hext : IsExtreme S r) (hgap : RankAdjacent S a b) :
    CarrierInterval (eventComponent events b) S ∧ IsExtreme (eventComponent events b) b := by sorry

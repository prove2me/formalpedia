-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_component_inside_hull
-- name    : LX.Core.ZeroGap.component_inside_hull
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:19:42.459028+00:00
-- url     : https://prove2.me/theorems/c475009d-5541-4806-96fc-42a5a4f9ed18
-- title:
--   A component inside another hull remains strictly inside
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. An event list $E$ consists of pairs $(x,y)\in I_n^2$, regarded as undirected graph edges. Let $C_E(r)$ be the graph component of $r$, $E_r$ the subsequence of events in that component, $E_{\rm out}(r)$ its complementary subsequence, and $\pi_E$ the ordered product of the corresponding transpositions. Assume each edge is oriented increasingly, and every later event has both endpoints outside the open interval between the endpoints of every earlier event. Let $n>0$, suppose $a<b<z$, $a,z$ are connected, and $a,b$ are disconnected. Let $\ell,h\in\mathbb N$ bound all vertices of $C_E(a)$ by $\ell\le i\le h$. Then
--
--   $$
--   j\in C_E(b)\Rightarrow\ell<j<h.
--   $$
--
--   Separated event geometry traps a disconnected interior component strictly inside the outer component hull.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LinearEventComponents.lean#L54-L73

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

theorem LX.Core.ZeroGap.component_inside_hull (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (a b z : Fin n) (ha : a.val < b.val) (hz : b.val < z.val)
    (haz : EventReaches events a z) (havoid : ¬EventReaches events a b)
    (lo hi : ℕ) (hbound : ∀ i, EventReaches events a i → lo ≤ i.val ∧ i.val ≤ hi)
    (j : Fin n) (hbj : EventReaches events b j) : lo < j.val ∧ j.val < hi := by sorry

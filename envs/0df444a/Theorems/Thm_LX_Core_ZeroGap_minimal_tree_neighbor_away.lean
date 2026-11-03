-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_minimal_tree_neighbor_away
-- name    : LX.Core.ZeroGap.minimal_tree_neighbor_away
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:20:25.41157+00:00
-- url     : https://prove2.me/theorems/ce6ee121-551c-486a-9be3-bc72ac494947
-- title:
--   A minimal separated event tree has a neighbor away from an extreme
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. An event list $E$ consists of pairs $(x,y)\in I_n^2$, regarded as undirected graph edges. Let $C_E(r)$ be the graph component of $r$, $E_r$ the subsequence of events in that component, $E_{\rm out}(r)$ its complementary subsequence, and $\pi_E$ the ordered product of the corresponding transpositions. Assume each edge is oriented increasingly, and every later event has both endpoints outside the open interval between the endpoints of every earlier event. Two vertices are rank adjacent in a set if they are distinct members with no member strictly between them in the linear order. An extreme vertex is at or beyond one end of the set. Let $n>0$, assume $|E|+1=|C_E(r)|\ge3$, and suppose $r$ is extreme in its component. Then
--
--   $$
--   \exists x,y\in C_E(r):\ x,y\text{ rank adjacent},\quad\pi_E(x)=y,\quad x\ne r,\ y\ne r.
--   $$
--
--   The neighbor can be chosen without using the distinguished extreme vertex.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/EventTreeRankNeighbor.lean#L10-L56

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

theorem LX.Core.ZeroGap.minimal_tree_neighbor_away (events : List (Event n)) (root : Fin n)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (hmin : events.length+1=(eventComponent events root).card)
    (hcard : 3 ≤ (eventComponent events root).card)
    (hext : IsExtreme (eventComponent events root) root) : NeighborAway events root root := by sorry

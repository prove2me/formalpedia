-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_root_cover_count
-- name    : LX.Core.ZeroGap.root_cover_count
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:59:10.41903+00:00
-- url     : https://prove2.me/theorems/0b5744c1-86eb-4496-9587-c8d8b796e97c
-- title:
--   Roots covering all event components bound the total vertex count by events plus roots
-- statement:
--   Let $n>0$, let $L$ be a finite list of ordered pairs of positions in $\mathbb Z/n\mathbb Z$, and let $R$ be a finite list of root positions. Regard each pair of $L$ as an undirected edge. Suppose every position is connected by these edges to at least one root in $R$, allowing a path of length zero. Then
--
--   $$
--   n\le |L|+|R|.
--   $$
--
--   Both lengths count repetitions: edges and roots need not be distinct. This rooted covering estimate controls how many vertices can be reached with a prescribed number of endpoint events.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapRootCoverCount.lean#L30-L48

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
variable {n : ℕ} [NeZero n]

theorem LX.Core.ZeroGap.root_cover_count (events : List (Event n)) (roots : List (Fin n))
    (hcover : ∀ i : Fin n, ∃ r ∈ roots, EventReaches events r i) :
    n ≤ events.length+roots.length := by sorry

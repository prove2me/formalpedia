-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_rank_adjacent_after_extreme_insertion
-- name    : LX.Core.ZeroGap.rank_adjacent_after_extreme_insertion
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:19:47.115144+00:00
-- url     : https://prove2.me/theorems/cd873691-fa39-4f2d-b4aa-541ef12b98b7
-- title:
--   Rank adjacency survives insertion next to an extreme
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Two vertices are rank adjacent in a set if they are distinct members with no member strictly between them in the linear order. An extreme vertex is at or beyond one end of the set. Let $n>0$, $T\subseteq I_n$, and $a,b\in I_n$. Suppose $a$ is extreme in $T\cup\{b\}$ and $a,b$ are rank adjacent there. If $x,y$ are rank adjacent in $T$, with $x,y\ne a$, then
--
--   $$
--   x,y\text{ are rank adjacent in }T\cup\{b\}.
--   $$
--
--   Inserting a vertex next to an extreme cannot split another neighboring pair.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ExtremeNeighborInsertion.lean#L17-L37

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

theorem LX.Core.ZeroGap.rank_adjacent_after_extreme_insertion (T : Finset (Fin n)) (a b : Fin n)
    (hext : IsExtreme (insert b T) a) (hgap : RankAdjacent (insert b T) a b)
    {x y : Fin n} (hxy : RankAdjacent T x y) (hxa : x ≠ a) (hya : y ≠ a) :
    RankAdjacent (insert b T) x y := by sorry

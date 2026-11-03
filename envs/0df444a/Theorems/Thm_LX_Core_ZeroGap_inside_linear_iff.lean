-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_inside_linear_iff
-- name    : LX.Core.ZeroGap.inside_linear_iff
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:02:36.548061+00:00
-- url     : https://prove2.me/theorems/cd008e71-b5f8-458f-b3c8-e36625afdbb3
-- title:
--   The clockwise interior of a linearly oriented event is its ordinary open interval
-- statement:
--   Let $n>0$ and identify positions with residues modulo $n$, using representatives $0,\ldots,n-1$ for comparisons. An event $e=(a,b)$ has clockwise interior consisting of positions whose positive clockwise distance from $a$ is smaller than the clockwise distance from $a$ to $b$. If $a<b$ in representative order, then, for every position $i$,
--
--   $$
--   i\in\operatorname{Inside}(a,b)\quad\Longleftrightarrow\quad a<i<b.
--   $$
--
--   Thus an event that does not wrap across the chosen cut has exactly its ordinary linear open interval as interior. This permits interval arguments to be applied to cyclic event geometry.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LinearEventComponents.lean#L11-L23

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

theorem LX.Core.ZeroGap.inside_linear_iff (e : Event n) (he : e.1.val < e.2.val) (i : Fin n) :
    Inside e i ↔ e.1.val < i.val ∧ i.val < e.2.val := by sorry

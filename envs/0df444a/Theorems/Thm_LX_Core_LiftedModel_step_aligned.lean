-- Prove2me | Theorems.Thm_LX_Core_LiftedModel_step_aligned
-- name    : LX.Core.LiftedModel.step_aligned
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:08.529892+00:00
-- url     : https://prove2.me/theorems/0d1c8ba3-e0f0-4bd2-9039-65c9a3af7475
-- title:
--   Every generator preserves lifted alignment
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. A lifted configuration records integer positions $x_i$, an integer cursor $c$, a physical cursor $\bar c\in I_n$, and a physical token permutation $t$. It is aligned when $c\bmod n=\bar c$ and $x_i\bmod n=t^{-1}(i)$. Let $n\ge2$ and let $a$ be a forward rotation, backward rotation, or head exchange in the core generator alphabet. Then
--
--   $$
--   s\text{ aligned}\Rightarrow\operatorname{step}(a,s)\text{ aligned}.
--   $$
--
--   The physical and integer models remain compatible under each elementary operation.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LiftedModel.lean#L44-L73

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel

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
namespace List
end List

namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
open LX
open LX.Core
open LX.Core.LiftedModel
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.Core.LiftedModel.step_aligned (hn : 2 ≤ n) (a : Letter) {s : Configuration n}
    (hs : Aligned s) : Aligned (step a s) := by sorry

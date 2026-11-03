-- Prove2me | Theorems.Thm_LX_Core_LiftedModel_x_as_pair_rename
-- name    : LX.Core.LiftedModel.x_as_pair_rename
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:15.330576+00:00
-- url     : https://prove2.me/theorems/56e53bb1-f284-4515-9696-ed1a783d1c65
-- title:
--   A lifted exchange is a periodic pair renaming
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. A lifted configuration records integer positions $x_i$, an integer cursor $c$, a physical cursor $\bar c\in I_n$, and a physical token permutation $t$. It is aligned when $c\bmod n=\bar c$ and $x_i\bmod n=t^{-1}(i)$. Let $n>0$, let $a\ne b$, and suppose the physical head and its successor contain labels $a$ and $b$. Write $x_i$ for their integer positions, and set $s_0=x_a+1-x_b$. Then
--
--   $$
--   \operatorname{step}(X,s)=\operatorname{rename}_{a,b,s_0}(s),
--   $$
--
--   Here the renaming swaps the physical labels, replaces $x_a$ by $x_b+s_0$ and $x_b$ by $x_a-s_0$, fixes all other positions, and leaves the cursor unchanged. This realizes an exchange as a periodic involution.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LiftedPair.lean#L36-L60

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
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_PhysicalModel

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
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.Core.LiftedModel.x_as_pair_rename (s : Configuration n) (a b : Fin n) (hab : a ≠ b)
    (ha : s.physical.tokens s.physical.cursor=a)
    (hb : s.physical.tokens (s.physical.cursor+1)=b) :
    step .x s=pairRename a b (s.position a+1-s.position b) s := by sorry

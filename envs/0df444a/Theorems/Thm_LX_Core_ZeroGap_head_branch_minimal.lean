-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_head_branch_minimal
-- name    : LX.Core.ZeroGap.head_branch_minimal
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:19:36.243375+00:00
-- url     : https://prove2.me/theorems/669a8617-9041-4736-a243-feec856d8364
-- title:
--   Deleting a minimal head edge leaves minimal branches
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. An event list $E$ consists of pairs $(x,y)\in I_n^2$, regarded as undirected graph edges. Let $C_E(r)$ be the graph component of $r$, $E_r$ the subsequence of events in that component, $E_{\rm out}(r)$ its complementary subsequence, and $\pi_E$ the ordered product of the corresponding transpositions. Let $n>0$, $E=e::T$, $e=(a,b)$, and assume $|E|+1=|C_E(a)|$. Then
--
--   $$
--   |T_a|+1=|C_T(a)|,\qquad |T_b|+1=|C_T(b)|.
--   $$
--
--   Both tail branches inherit the sharp spanning count from the whole head component.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/EventTreeBranchCounts.lean#L55-L72

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
import Definitions.Def_LX_ZeroGapComponentCounting
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

theorem LX.Core.ZeroGap.head_branch_minimal (e : Event n) (events : List (Event n))
    (hminimal : (e::events).length+1=(eventComponent (e::events) e.1).card) :
    (componentEvents events e.1).length+1=(eventComponent events e.1).card ∧
    (componentEvents events e.2).length+1=(eventComponent events e.2).card := by sorry

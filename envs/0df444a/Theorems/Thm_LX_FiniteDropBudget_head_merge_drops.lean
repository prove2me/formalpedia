-- Prove2me | Theorems.Thm_LX_FiniteDropBudget_head_merge_drops
-- name    : LX.FiniteDropBudget.head_merge_drops
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:25:24.772734+00:00
-- url     : https://prove2.me/theorems/0b1a675e-3a67-43d2-bd1d-7f823b799da7
-- title:
--   Head merging preserves descending and backward-unit positions
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Let $n>0$, let $p$ permute $I_n$, and choose $b>0$ with $p(0)=b<p(b)$. Put $q=p\circ(0\ b)$ and $M(p)=\sum_i|p(i)-i|$. Write $D(p)=\{i:p(i)<i\}$ and $U(p)=\{i:p(i)+1=i\}$, using ordinary representatives. Then
--
--   $$
--   D(q)=D(p),\qquad U(q)=U(p).
--   $$
--
--   Both drop statistics survive contraction of the forward head chain.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FiniteChainMerge.lean#L104-L124

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
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteDropBudget
import Definitions.Def_LX_Graph

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
namespace LX.Core.FiniteGaps
end LX.Core.FiniteGaps
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
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
namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
namespace List
end List

namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
open LX
open LX.FiniteDropBudget
open scoped BigOperators
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem LX.FiniteDropBudget.head_merge_drops (p : LX.Core.State n) (b : Fin n)
    (hb : 0 < b.val) (hhead : p 0=b) (hnext : b.val < (p b).val) :
    descendingPositions (p*Equiv.swap 0 b)=descendingPositions p ∧
      backwardUnits (p*Equiv.swap 0 b)=backwardUnits p := by sorry

-- Prove2me | Theorems.Thm_LX_FiniteDropBudget_head_merge_inversions
-- name    : LX.FiniteDropBudget.head_merge_inversions
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:24:46.169934+00:00
-- url     : https://prove2.me/theorems/2203c236-dc52-4f1a-8a68-58af2d4bcada
-- title:
--   Head merging increases inversions by one
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Let $n>0$, let $p$ permute $I_n$, and choose $b>0$ with $p(0)=b<p(b)$. Put $q=p\circ(0\ b)$ and $M(p)=\sum_i|p(i)-i|$. Assume additionally $p(j)=j$ for $0<j<b$. Then
--
--   $$
--   \operatorname{inv}(q)=\operatorname{inv}(p)+1.
--   $$
--
--   Merging a forward head chain has a controlled exact inversion price.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FiniteChainMerge.lean#L12-L76

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
import Definitions.Def_LX_FiniteWindowInversions
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

theorem LX.FiniteDropBudget.head_merge_inversions (p : LX.Core.State n) (b : Fin n)
    (hb : 0 < b.val) (hhead : p 0=b) (hnext : b.val < (p b).val)
    (hfix : ∀ j : Fin n,0 < j.val → j.val < b.val → p j=j) :
    inversionNumber (p*Equiv.swap 0 b)=inversionNumber p+1 := by sorry

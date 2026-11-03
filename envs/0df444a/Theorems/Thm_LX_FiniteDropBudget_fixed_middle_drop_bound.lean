-- Prove2me | Theorems.Thm_LX_FiniteDropBudget_fixed_middle_drop_bound
-- name    : LX.FiniteDropBudget.fixed_middle_drop_bound
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:24:58.556973+00:00
-- url     : https://prove2.me/theorems/83b4a721-502f-4049-924b-922004e77bf4
-- title:
--   A fixed middle block reduces the drop budget
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For a permutation $p$, write $d(p)=|\{i:p(i)<i\}|$, $u(p)=|\{i:p(i)+1=i\}|$, $M(p)=\sum_i|p(i)-i|$, and $J(p)=\operatorname{inv}(p)$; all comparisons use integer representatives. Let $n=k+1$, let $0\le r\le n$, assume $p(0)\ne0,k$, and suppose $p(i)=i$ for $0<i<r$. Then
--
--   $$
--   3d(p)\le n-r+M(p)-J(p)+u(p).
--   $$
--
--   A movable head can be retained while the fixed middle block is removed from the effective budget.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FinitePrefixRotation.lean#L81-L99

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
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteDropBudget
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
variable {k : ℕ}

theorem LX.FiniteDropBudget.fixed_middle_drop_bound (p : LX.Core.State (k+1)) (r : ℕ)
    (hr : r ≤ k+1) (hp : p 0 ≠ 0) (hlast : p 0 ≠ Fin.last k)
    (hfix : ∀ i : Fin (k+1),0 < i.val → i.val < r → p i=i) :
    3*((descendingPositions p).card : ℤ) ≤ ((k+1 : ℕ) : ℤ)-(r : ℤ)+
      (∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|)-(inversionNumber p : ℤ)+(backwardUnits p).card := by sorry

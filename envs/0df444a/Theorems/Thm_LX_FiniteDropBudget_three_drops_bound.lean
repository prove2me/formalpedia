-- Prove2me | Theorems.Thm_LX_FiniteDropBudget_three_drops_bound
-- name    : LX.FiniteDropBudget.three_drops_bound
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:11:58.465398+00:00
-- url     : https://prove2.me/theorems/bc681945-e7d5-471a-b94a-3e57d301baa5
-- title:
--   Three-drop bound for a nonempty finite permutation
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For a permutation $p$, write $d(p)=|\{i:p(i)<i\}|$, $u(p)=|\{i:p(i)+1=i\}|$, $M(p)=\sum_i|p(i)-i|$, and $J(p)=\operatorname{inv}(p)$; all comparisons use integer representatives. Let $k\in\mathbb N$ and let $p$ permute $I_{k+1}$. Then, as an integer inequality,
--
--   $$
--   3d(p)\le k+M(p)-J(p)+u(p).
--   $$
--
--   The drop budget relates descending arrows to displacement and inversion savings.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FiniteDropBudget.lean#L53-L88

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

theorem LX.FiniteDropBudget.three_drops_bound {k : ℕ} (p : LX.Core.State (k+1)) :
    3*((descendingPositions p).card : ℤ) ≤ (k+1 : ℤ)+
      (∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|)-(inversionNumber p : ℤ)+
        (backwardUnits p).card-1 := by sorry

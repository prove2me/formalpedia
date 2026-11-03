-- Prove2me | Theorems.Thm_LX_FiniteDropBudget_contract_forward_prefix
-- name    : LX.FiniteDropBudget.contract_forward_prefix
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:25:35.683208+00:00
-- url     : https://prove2.me/theorems/e307dcce-a839-4227-8c19-de28903358a8
-- title:
--   Contracting a forward prefix
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For a permutation $p$, write $d(p)=|\{i:p(i)<i\}|$, $u(p)=|\{i:p(i)+1=i\}|$, $M(p)=\sum_i|p(i)-i|$, and $J(p)=\operatorname{inv}(p)$; all comparisons use integer representatives. Say the prefix of length $r$ is forward when every $i<r$ has $p(i)\ge i$ and every $j$ strictly between $i$ and $p(i)$ is fixed. Let $n>0$, $r>0$, assume the forward-prefix condition and $p(0)\ne0$. Then there is a permutation $q$ with
--
--   $$
--   q(i)=i\ (0<i<r),\quad q\text{ has a forward prefix of length }r,\quad q(0)\ne0,\quad D(q)=D(p),\quad U(q)=U(p),\quad M(q)-J(q)\le M(p)-J(p).
--   $$
--
--   Here $D$ and $U$ are the descending and backward-unit sets. The contraction preserves the drop data needed for later estimates.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ForwardPrefixContraction.lean#L57-L102

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
import Definitions.Def_LX_ForwardPrefixContraction
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

theorem LX.FiniteDropBudget.contract_forward_prefix (p : LX.Core.State n) (r : ℕ) (hr : 0 < r)
    (hp : ForwardPrefix p r) (hhead : p 0 ≠ 0) :
    ∃ q : LX.Core.State n,
      (∀ i : Fin n,0 < i.val → i.val < r → q i=i) ∧
      ForwardPrefix q r ∧ q 0 ≠ 0 ∧
      descendingPositions q=descendingPositions p ∧ backwardUnits q=backwardUnits p ∧
      (∑ i, |_root_.LX.Core.FiniteCuts.displacement q i|)-(inversionNumber q : ℤ) ≤
        (∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|)-(inversionNumber p : ℤ) := by sorry

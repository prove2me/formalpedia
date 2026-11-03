-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_shifted_balanced_descending_count
-- name    : LX.Core.FiniteCuts.shifted_balanced_descending_count
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:58:27.259301+00:00
-- url     : https://prove2.me/theorems/41819107-36ad-462a-8ede-65fb7bf4ce88
-- title:
--   A balanced shifted strip counts descending positions
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Let $n>0$, let $p$ permute $I_n$, and let $d:I_n\to\mathbb Z$ and $h\in\mathbb Z$. Assume balance, $0\le d_i+h<n$, and $i+d_i+h\equiv p(i)\pmod n$. Then
--
--   $$
--   |\{i:p(i)<i\}|=h.
--   $$
--
--   The integer shift of a balanced strip is determined by the number of arrows that cross the linear cut.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ClockwiseLiftCount.lean#L50-L67

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
namespace List
end List

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem LX.Core.FiniteCuts.shifted_balanced_descending_count [NeZero n] (p : State n)
    (d : Fin n → ℤ) (h : ℤ) (hbalance : ∑ i, d i=0)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ))
    (hmod : ∀ i : Fin n, Int.ModEq (n : ℤ) ((i : ℤ)+d i+h) (p i : ℤ)) :
    ((descendingPositions p).card : ℤ)=h := by sorry

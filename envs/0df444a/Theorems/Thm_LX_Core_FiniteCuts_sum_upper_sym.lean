-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_sum_upper_sym
-- name    : LX.Core.FiniteCuts.sum_upper_sym
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:58:20.915556+00:00
-- url     : https://prove2.me/theorems/967f51c3-9ab4-437c-a3c1-a6d0dba82029
-- title:
--   Symmetrizing a double sum over the strict upper triangle
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Let $n\in\mathbb N$ and $f:I_n\times I_n\to\mathbb Z$ satisfy $f(i,i)=0$ for every $i$. Then
--
--   $$
--   \sum_{i<j}(f(i,j)+f(j,i))=\sum_i\sum_j f(i,j).
--   $$
--
--   This groups both orientations of every off-diagonal pair into one ordered pair.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FiniteCrossPairCount.lean#L8-L27

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

theorem LX.Core.FiniteCuts.sum_upper_sym (f : Fin n → Fin n → ℤ) (hd : ∀ i, f i i=0) :
    (∑ i, ∑ j, if i < j then f i j+f j i else 0) = ∑ i, ∑ j, f i j := by sorry

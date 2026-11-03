-- Prove2me | Theorems.Thm_LX_Core_FiniteWindow_sum_window_nat
-- name    : LX.Core.FiniteWindow.sum_window_nat
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:58:34.054765+00:00
-- url     : https://prove2.me/theorems/7672b728-464a-4187-9d65-205093801933
-- title:
--   Summing a natural-valued function supported on a window
-- statement:
--   Let $n,b\in\mathbb N$ and choose an integer window offset $o\ge0$ with $o+b\le n$. Its embedding is $e(i)=o+i$ from $I_b$ into $I_n$, and its carrier is $W=\{o,\ldots,o+b-1\}$. Let $f:I_n\to\mathbb N$ vanish outside $W$. Then
--
--   $$
--   \sum_{j\in I_n}f(j)=\sum_{i\in I_b}f(e(i)).
--   $$
--
--   A supported ambient sum reduces to its window coordinates, including an empty window.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FiniteWindowInversions.lean#L46-L59

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
import Definitions.Def_LX_FiniteWindow

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

namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
open LX
open LX.Core
open LX.Core.FiniteWindow
open scoped BigOperators
variable {n b : ℕ}

theorem LX.Core.FiniteWindow.sum_window_nat (W : Window n b) (f : Fin n → ℕ)
    (hzero : ∀ j, ¬Contains W j → f j=0) :
    (∑ j : Fin n, f j)=∑ i : Fin b, f (embed W i) := by sorry

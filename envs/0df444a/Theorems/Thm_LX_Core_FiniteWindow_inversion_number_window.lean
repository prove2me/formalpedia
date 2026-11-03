-- Prove2me | Theorems.Thm_LX_Core_FiniteWindow_inversion_number_window
-- name    : LX.Core.FiniteWindow.inversion_number_window
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:58:37.252051+00:00
-- url     : https://prove2.me/theorems/d7d3e23a-fbaa-4edf-9f5d-65de1ede0a98
-- title:
--   A window extension preserves inversion number
-- statement:
--   Let $n,b\in\mathbb N$ and choose an integer window offset $o\ge0$ with $o+b\le n$. Its embedding is $e(i)=o+i$ from $I_b$ into $I_n$, and its carrier is $W=\{o,\ldots,o+b-1\}$. Let $p$ permute $I_b$, and extend it to $\widetilde p$ on $I_n$ by $\widetilde p(e(i))=e(p(i))$ and fixing every point outside $W$. Then
--
--   $$
--   \operatorname{inv}(\widetilde p)=\operatorname{inv}(p).
--   $$
--
--   Increasing interval extension does not introduce any new inversions.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FiniteWindowInversions.lean#L87-L103

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

theorem LX.Core.FiniteWindow.inversion_number_window (W : Window n b) (p : State b) :
    FiniteCuts.inversionNumber (permutation W p)=FiniteCuts.inversionNumber p := by sorry

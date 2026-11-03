-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_inverse_rotate_int
-- name    : LX.Core.FiniteCuts.inverse_rotate_int
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:18:30.273427+00:00
-- url     : https://prove2.me/theorems/f4203ae6-4dab-44bc-a7f8-abf284e99506
-- title:
--   Integer formula for inverse cyclic rotation
-- statement:
--   Let $k\in\mathbb N$, let $n=k+1$, and let $A(i)=i+1\pmod n$ on $I_n$. For every integer representative $i\in I_n$,
--
--   $$
--   [A^{-1}(i)]_n=i-1+n\mathbf1_{i=0}.
--   $$
--
--   The formula records the exact seam correction when moving the cut backward by one position.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FiniteEnergyRotation.lean#L10-L22

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
variable {k : ℕ}

theorem LX.Core.FiniteCuts.inverse_rotate_int (i : Fin (k+1)) :
    ((finRotate (k+1)).symm i : ℤ)=(i : ℤ)-1+(if i=0 then (k+1 : ℤ) else 0) := by sorry

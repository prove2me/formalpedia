-- Prove2me | Theorems.Thm_LX_CenteredLift_even_reflection_board_sum
-- name    : LX.CenteredLift.even_reflection_board_sum
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:07:12.179203+00:00
-- url     : https://prove2.me/theorems/c39bad43-f5af-449d-98e9-7c261fff6e55
-- title:
--   Mass of a centered even reflection board
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Write $\operatorname{cent}_m(x)=((x+m)\bmod n)-m$, the unique representative in $[-m,n-m)$. Let $m>0$, $n=2m$, $C\in\mathbb Z$, and $r_i=\operatorname{cent}_m(C-2i)$. Then
--
--   $$
--   \sum_i r_i=n\big((C+m)\bmod2-1\big).
--   $$
--
--   The reflection-board mass is either $-n$ or zero, according to parity.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/EvenCenteredMass.lean#L47-L72

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
import Definitions.Def_LX_OddCenteredMass

namespace Int
end Int
namespace LX
end LX
namespace LX.CenteredLift
end LX.CenteredLift
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace List
end List

namespace LX.CenteredLift
end LX.CenteredLift
open LX
open LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.CenteredLift.even_reflection_board_sum (m : ℕ) (hm : 0 < m) (hn : n=2*m) (C : ℤ) :
    (∑ i : Fin n,reflectionBoard m C i)=(n : ℤ)*((C+m)%2-1) := by sorry

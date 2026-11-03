-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_adjacent_boundary_mass_price
-- name    : LX.Core.FiniteCuts.adjacent_boundary_mass_price
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:09.567483+00:00
-- url     : https://prove2.me/theorems/b7898140-8c5c-4f50-8940-e4154adc00e7
-- title:
--   Mass price of joining adjacent arrows
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Let $n\in\mathbb N$, let $p$ permute $I_n$, and let $a,b\in I_n$ satisfy $b=a+1$, $p(a)\le a$, and $b\le p(b)$. Put $\delta_p(i)=p(i)-i$. Then
--
--   $$
--   \sum_i|\delta_{p\circ(a\ b)}(i)|=\sum_i|\delta_p(i)|+2.
--   $$
--
--   This local identity measures the exact change in total displacement when two adjacent arrows are joined.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AdjacentBoundaryPrice.lean#L8-L31

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

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem LX.Core.FiniteCuts.adjacent_boundary_mass_price (p : State n) (a b : Fin n)
    (hadj : b.val=a.val+1) (ha : (p a).val ≤ a.val) (hb : b.val ≤ (p b).val) :
    (∑ i, |_root_.LX.Core.FiniteCuts.displacement (p*Equiv.swap a b) i|)=(∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|)+2 := by sorry

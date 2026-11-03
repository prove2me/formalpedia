-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_involutive_of_cycles_are_swaps
-- name    : LX.Core.FiniteCuts.involutive_of_cycles_are_swaps
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:03:27.620787+00:00
-- url     : https://prove2.me/theorems/0bb5fe3c-bac0-4664-9e50-f3b370bebfbd
-- title:
--   A permutation whose nontrivial cycles are transpositions is an involution
-- statement:
--   Let $n$ be any natural number and let $p$ be a permutation of $\{0,\ldots,n-1\}$. Suppose every nontrivial factor in the disjoint cycle decomposition of $p$ is a transposition. Then $p$ is an involution:
--
--   $$
--   \forall i\in\{0,\ldots,n-1\},\qquad p(p(i))=i.
--   $$
--
--   Fixed points are permitted, and the assertion also covers the empty permutation. This connects the cycle-factor description of a permutation with the pointwise involution property needed in matching geometry.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LinearMatchingGeometry.lean#L12-L26

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
import Definitions.Def_LX_Graph

namespace LX.Core
end LX.Core
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
variable {n : ℕ}

theorem LX.Core.FiniteCuts.involutive_of_cycles_are_swaps (p : State n)
    (hp : ∀ q ∈ p.cycleFactorsFinset, q.IsSwap) : Function.Involutive p := by sorry

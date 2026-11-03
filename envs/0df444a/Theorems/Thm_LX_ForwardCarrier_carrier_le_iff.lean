-- Prove2me | Theorems.Thm_LX_ForwardCarrier_carrier_le_iff
-- name    : LX.ForwardCarrier.carrier_le_iff
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:05:48.00274+00:00
-- url     : https://prove2.me/theorems/7cbe481a-8faf-4433-9cd0-1c00a5182c9d
-- title:
--   The forward carrier is the prefix maximum
-- statement:
--   Let $F:\mathbb N\to\mathbb Z$. Starting with the values $F(j)$, compare neighboring entries successively at $0,1,\ldots,k-1$, leaving their larger value on the right. Let $c_k$ be the resulting value at position $k$. Then, for $x\in\mathbb Z$,
--
--   $$
--   c_k\le x\iff\forall j\le k,\ F(j)\le x.
--   $$
--
--   This identifies the upper-bound behavior of the carrier used in forward scan arguments.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ForwardCarrier.lean#L26-L39

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
import Definitions.Def_LX_ForwardCarrier

namespace Int
end Int
namespace LX
end LX
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace List
end List

namespace LX.ForwardCarrier
end LX.ForwardCarrier
open LX
open LX.ForwardCarrier

theorem LX.ForwardCarrier.carrier_le_iff (F : ℕ → ℤ) (k : ℕ) (x : ℤ) :
    sweepPrefix F k k ≤ x ↔ ∀ j ≤ k, F j ≤ x := by sorry

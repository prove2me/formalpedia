-- Prove2me | Theorems.Thm_LX_DirectedTokenLower_word_endpoint_lift
-- name    : LX.DirectedTokenLower.word_endpoint_lift
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:02:32.961209+00:00
-- url     : https://prove2.me/theorems/62649c79-03b4-481b-87cb-7ddcf2fe5e49
-- title:
--   An actual word supplies its endpoint lift
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. A balanced lift of a permutation $p$ with phase $c$ means $\sum_i d_i=0$ and $i+d_i\equiv p^{-1}(i)+c\pmod n$. Let $n\ge2$. Run $w$ from the initial lifted configuration, with token $i$ initially at integer position $i$ and cursor zero. Let $x_i$ be its final integer position and $c$ its final cursor. Then
--
--   $$
--   d_i=x_i-i\quad\Longrightarrow\quad d\text{ is a balanced lift of }\operatorname{ev}(w)\text{ at }c.
--   $$
--
--   The lift and its phase come from one literal word endpoint.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/DirectedLiftLower.lean#L10-L32

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
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
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
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace List
end List

namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
open LX
open LX.DirectedTokenLower
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.LiftedModel LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.DirectedTokenLower.word_endpoint_lift (hn : 2 ≤ n) (w : List Letter) :
    IsLift (eval (n := n) w) (run (w.map Letter.toCore) (initial (n := n))).cursor
      (fun i => (run (w.map Letter.toCore) (initial (n := n))).position i-(i : ℤ)) := by sorry

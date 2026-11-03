-- Prove2me | Theorems.Thm_LX_Core_LiftedModel_repeated_of_not_nodup
-- name    : LX.Core.LiftedModel.repeated_of_not_nodup
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:33.850161+00:00
-- url     : https://prove2.me/theorems/9309156b-0179-4a78-8ed1-052ff0b82293
-- title:
--   A repeated event list yields two matching exchange occurrences
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. Let $n>0$, let $s$ be a lifted configuration, and record at each $X$ its periodic token-pair key, which retains the two token labels and their relative full-period offset. If the event list of $w$ has a repetition, then
--
--   $$
--   w=uXvXz\quad\text{for some }u,v,z,\qquad\operatorname{key}(\operatorname{run}(u,s))=\operatorname{key}(\operatorname{run}(uXv,s)).
--   $$
--
--   This turns a repeated list entry into the concrete pair of exchanges needed for deletion.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/EventTrace.lean#L45-L62

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
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_PairEvents

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
namespace List
end List

namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
open LX
open LX.Core
open LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]

theorem LX.Core.LiftedModel.repeated_of_not_nodup (w : List Letter) (s : Configuration n)
    (h : ¬ (events w s).Nodup) : RepeatedEvents w s := by sorry

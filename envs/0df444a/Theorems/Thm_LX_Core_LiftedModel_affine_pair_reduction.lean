-- Prove2me | Theorems.Thm_LX_Core_LiftedModel_affine_pair_reduction
-- name    : LX.Core.LiftedModel.affine_pair_reduction
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:35.219553+00:00
-- url     : https://prove2.me/theorems/00ea7b01-f915-401b-9314-0c4f342db855
-- title:
--   Removing repeated lifted pair events
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. Let $n\ge2$, let $s$ be a lifted configuration (integer token positions and cursor), and let $w$ be any word. Record the periodically identified token pair at each exchange as its event. Then
--
--   $$
--   \exists v\preceq w:\quad\operatorname{run}(v,s)=\operatorname{run}(w,s),\quad\operatorname{rot}(v)=\operatorname{rot}(w),\quad\operatorname{events}(v,s)\text{ has no repetitions},\quad |v|\le |w|.
--   $$
--
--   Here $v\preceq w$ means deletion of letters, and $\operatorname{rot}$ retains the rotation subsequence. This reduction preserves the full lifted endpoint.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AffineDeletion.lean#L18-L53

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
import Definitions.Def_LX_AffineDeletion
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
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
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

theorem LX.Core.LiftedModel.affine_pair_reduction (hn : 2 ≤ n) (w : List Letter) (s : Configuration n) :
    ∃ v : List Letter, run v s=run w s ∧ rotationLetters v=rotationLetters w ∧
      (events v s).Nodup ∧ v.length ≤ w.length ∧ v.Sublist w := by sorry

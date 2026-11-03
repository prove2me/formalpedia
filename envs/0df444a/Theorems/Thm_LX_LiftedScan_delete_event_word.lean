-- Prove2me | Theorems.Thm_LX_LiftedScan_delete_event_word
-- name    : LX.LiftedScan.delete_event_word
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:18.244678+00:00
-- url     : https://prove2.me/theorems/37cf8e75-bccd-4f66-b55f-2a7703230d77
-- title:
--   Deleting a recorded exchange from a sorting word
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. Let $n\ge2$, suppose $p\operatorname{ev}(w)=1$, and let a periodic pair key $k=(a,b,\text{shift})$ occur in the lifted event list of $w$ from the initial configuration. Then
--
--   $$
--   \exists v:\quad p(a\ b)\operatorname{ev}(v)=1,\quad|v|+1=|w|,\quad\#_L(v)=\#_L(w).
--   $$
--
--   A recorded lifted crossing gives a one-exchange shortening after the corresponding finite label swap.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LiftedScanBridge.lean#L139-L158

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
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
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
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.LiftedScan
end LX.LiftedScan
namespace List
end List

namespace LX.LiftedScan
end LX.LiftedScan
open LX
open LX.LiftedScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.LiftedScan.delete_event_word (hn : 2 ≤ n) (p : State n) (w : List Letter)
    (hp : p*eval w=1) (key : LX.Core.LiftedModel.PairKey n)
    (hkey : key ∈ LX.Core.LiftedModel.events (w.map Letter.toCore) LX.Core.LiftedModel.initial) :
    ∃ v : List Letter,(p*Equiv.swap key.first key.second)*eval v=1 ∧
      v.length+1=w.length ∧ v.count .l=w.count .l := by sorry

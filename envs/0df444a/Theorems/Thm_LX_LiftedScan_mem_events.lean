-- Prove2me | Theorems.Thm_LX_LiftedScan_mem_events
-- name    : LX.LiftedScan.mem_events
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:19.914665+00:00
-- url     : https://prove2.me/theorems/b7ace218-c43f-4bcf-8baa-fd3dfc7fd336
-- title:
--   Membership in the two-letter lifted event list
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. Let $n>0$, let $s$ be a lifted configuration, and let $k$ be a periodic pair key recording two token labels and their relative copy offset. Then
--
--   $$
--   k\in\operatorname{events}(w,s)\iff\exists u,v:\ w=uXv,\quad\operatorname{key}(\operatorname{run}(u,s))=k.
--   $$
--
--   The two-letter word is interpreted in the core lifted model. Every recorded event is witnessed by a literal exchange position.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LiftedScanBridge.lean#L112-L137

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

theorem LX.LiftedScan.mem_events (w : List Letter) (s : LX.Core.LiftedModel.Configuration n)
    (key : LX.Core.LiftedModel.PairKey n) :
    key ∈ LX.Core.LiftedModel.events (w.map Letter.toCore) s ↔
      ∃ u v : List Letter,w=u++[.x]++v ∧
        LX.Core.LiftedModel.eventKey (LX.Core.LiftedModel.run (u.map Letter.toCore) s)=key := by sorry

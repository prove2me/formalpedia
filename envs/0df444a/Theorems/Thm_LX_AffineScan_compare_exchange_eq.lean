-- Prove2me | Theorems.Thm_LX_AffineScan_compare_exchange_eq
-- name    : LX.AffineScan.compare_exchange_eq
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:56.684813+00:00
-- url     : https://prove2.me/theorems/b77350c7-71e1-4776-ab1e-4e4a3b22e555
-- title:
--   Head comparison absorbs a prior exchange
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Let $E(d)_0=d_1+1$, $E(d)_1=d_0-1$, and $E(d)_i=d_i$ otherwise; let $Q(d)$ equal $E(d)$ when $d_1+1<d_0$ and equal $d$ otherwise. For $n\ge2$ and every integer board $d$,
--
--   $$
--   Q(E(d))=Q(d).
--   $$
--
--   Thus the comparison chooses the same ordered head regardless of the initial orientation of the two targets.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AffineRankOrder.lean#L173-L198

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
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_SweepCarrier

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
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace List
end List

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.AffineScan.compare_exchange_eq (hn : 2 ≤ n) (d : Fin n → ℤ) :
    compareHead (exchange d)=compareHead d := by sorry

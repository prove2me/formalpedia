-- Prove2me | Theorems.Thm_LX_LiftedScan_exact_positions_of_zero
-- name    : LX.LiftedScan.exact_positions_of_zero
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:21.320717+00:00
-- url     : https://prove2.me/theorems/1bc2a8e4-51f9-44c7-ba32-e1db6872b867
-- title:
--   A zero-board word has prescribed exact integer token positions
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. Let $n\ge2$, let $d:I_n\to\mathbb Z$, and suppose running $w$ on the affine board $d$ gives zero. Execute $w$ in the integer token model from initial positions $x_i=i$ and cursor zero. Then
--
--   $$
--   x_i^{\rm final}=i+d_i\qquad(i\in I_n).
--   $$
--
--   The equality is over integers and retains winding information beyond the endpoint residues.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LiftedScanBridge.lean#L70-L87

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
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

theorem LX.LiftedScan.exact_positions_of_zero (hn : 2 ≤ n) (d : Fin n → ℤ) (w : List Letter)
    (hz : ∀ i,AffineScan.run w d i=0) :
    ∀ i,(LX.Core.LiftedModel.run (w.map Letter.toCore) LX.Core.LiftedModel.initial).position i=
      (i : ℤ)+d i := by sorry

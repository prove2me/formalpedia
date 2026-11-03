-- Prove2me | Theorems.Thm_LX_Antipode_even_exception_lift
-- name    : LX.Antipode.even_exception_lift
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:06:58.616282+00:00
-- url     : https://prove2.me/theorems/3adc79a0-2e80-4648-bcac-07307c168d10
-- title:
--   The exceptional even board is a lift
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Define the candidate $p_{\mathrm e}=((i\mapsto1-i)\circ(1\ 2))^{-1}$. For $n=2m$, define $e_0=4-m$, $e_1=e_2=1-m$, $e_i=m+4-2i$ for $3\le i\le m+1$, and $e_i=3m+4-2i$ for $m+2\le i<2m$. A balanced lift of a permutation $p$ with phase $c$ means $\sum_i d_i=0$ and $i+d_i\equiv p^{-1}(i)+c\pmod n$. For $m\ge3$ and $n=2m$,
--
--   $$
--   e\text{ is a balanced lift of }p_{\mathrm e}\text{ at integer phase }m+3.
--   $$
--
--   This connects the explicit exceptional queue to the even antipode permutation.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/EvenBoundaryLower.lean#L14-L26

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
import Definitions.Def_LX_AntipodeCandidates
import Definitions.Def_LX_ExceptionalPrefixDelay

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Antipode
end LX.Antipode
namespace LX.CenteredLift
end LX.CenteredLift
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteGaps
end LX.Core.FiniteGaps
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace LX.FinitePairReduction
end LX.FinitePairReduction
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.LiftedScan
end LX.LiftedScan
namespace List
end List

namespace LX.Antipode
end LX.Antipode
open LX
open LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.Antipode.even_exception_lift (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    IsLift (even : State n) ((m+3 : ℕ) : ℤ) (evenException m) := by sorry

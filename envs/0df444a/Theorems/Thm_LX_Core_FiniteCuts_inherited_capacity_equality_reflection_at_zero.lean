-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_inherited_capacity_equality_reflection_at_zero
-- name    : LX.Core.FiniteCuts.inherited_capacity_equality_reflection_at_zero
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:04:11.3215+00:00
-- url     : https://prove2.me/theorems/386ecba7-bd46-4f29-8986-91e1e638ed5b
-- title:
--   Capacity equality gives a reflection at a fixed cut
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. A balanced lift of a permutation $p$ with phase $c$ means $\sum_i d_i=0$ and $i+d_i\equiv p^{-1}(i)+c\pmod n$. A board is majorized if $2\sum_{i\in S}d_i\le |S|(n-|S|)$ for every subset $S\subseteq I_n$. Let $n>0$, let $o,d:I_n\to\mathbb Z$, with $o$ balanced and majorized, and suppose $d$ lifts $p$ at phase $c$. Let $h\in\mathbb Z$ satisfy $n=2h+1$ or $n=2h+2$. Assume $0\le d_i+h<n$, $d_i\le h$, and $d_i=\pm h\Rightarrow o_i=\pm h$, with matching signs. Suppose the affine inversion count of targets $i+d_i$ equals $h(n-h-1)$. Put $q(i)=p^{-1}(i)+c+h$ modulo $n$ and assume $q(0)=0$. Then
--
--   $$
--   q(i)=-i\qquad(i\in I_n).
--   $$
--
--   The extremal inversion count rigidly determines the shifted endpoint permutation.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/CapacityEqualityReflectionAtZero.lean#L10-L40

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
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_StrictBandInversionCapacity

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
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped BigOperators Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.Core.FiniteCuts.inherited_capacity_equality_reflection_at_zero
    {p : State n} {phase : ℤ} {original d : Fin n → ℤ}
    (horiginal : ∑ i, original i=0) (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p phase d) (h : ℤ)
    (hparity : (n : ℤ)=2*h+1 ∨ (n : ℤ)=2*h+2)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ)) (hupper : ∀ i, d i ≤ h)
    (hinheritNeg : ∀ i, d i= -h → original i= -h)
    (hinheritPos : ∀ i, d i=h → original i=h)
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      h*((n : ℤ)-h-1))
    (hzero : shiftedLiftPermutation p phase h 0=0) :
    ∀ i, shiftedLiftPermutation p phase h i= -i := by sorry

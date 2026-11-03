-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_inherited_capacity_equality_noncrossing
-- name    : LX.Core.FiniteCuts.inherited_capacity_equality_noncrossing
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:02:56.030893+00:00
-- url     : https://prove2.me/theorems/114350ff-c998-4532-8cfa-4934b4d87e38
-- title:
--   Inherited capacity equality has noncrossing shifted pairs
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. A balanced lift of a permutation $p$ with phase $c$ means $\sum_i d_i=0$ and $i+d_i\equiv p^{-1}(i)+c\pmod n$. A board is majorized if $2\sum_{i\in S}d_i\le |S|(n-|S|)$ for every subset $S\subseteq I_n$. Let $n>0$, let $o$ be balanced and majorized, and let $d$ lift $p$ at integer phase $c$. Let $h\in\mathbb Z$ satisfy $2h\le n$, $0\le d_i+h<n$, and $d_i=-h\Rightarrow o_i=-h$. Suppose $I(d)=h(n-h-1)$. Put $q(i)=p^{-1}(i)+c+h$ modulo $n$. Then
--
--   $$
--   a<b<c<d,\quad q(a)=c\quad\Longrightarrow\quad q(b)\ne d.
--   $$
--
--   The equality case inherits the planar order needed for reflection rigidity.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FiniteShallowMatching.lean#L92-L116

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
open scoped BigOperators
variable {n : ℕ}

theorem LX.Core.FiniteCuts.inherited_capacity_equality_noncrossing [NeZero n]
    {p : State n} {phase : ℤ} {original disp : Fin n → ℤ}
    (horiginal : ∑ i, original i=0) (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p phase disp) (h : ℤ) (hh : 2*h ≤ (n : ℤ))
    (hband : ∀ i, 0 ≤ disp i+h ∧ disp i+h < (n : ℤ))
    (hinherit : ∀ i, disp i= -h → original i= -h)
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+disp i) : ℤ)=
      h*((n : ℤ)-h-1))
    (a b c d : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (hac : shiftedLiftPermutation p phase h a=c) : shiftedLiftPermutation p phase h b ≠ d := by sorry

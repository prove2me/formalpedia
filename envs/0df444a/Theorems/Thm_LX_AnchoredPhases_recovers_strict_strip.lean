-- Prove2me | Theorems.Thm_LX_AnchoredPhases_recovers_strict_strip
-- name    : LX.AnchoredPhases.recovers_strict_strip
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:00:15.248317+00:00
-- url     : https://prove2.me/theorems/a2504d6b-ec93-474b-8100-a7b93a92a494
-- title:
--   Recovering a balanced lift from a strict strip
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For a permutation $p$ and anchor $a$, let $q_a(i)=p(i)+a-p(a)$, $h_a=|\{i:q_a(i)<i\}|$, $D^a_i=((q_a(i)-i)\bmod n)-h_a$, and $c_a=a-p(a)-h_a$. A balanced lift of a permutation $p$ with phase $c$ means $\sum_i d_i=0$ and $i+d_i\equiv p^{-1}(i)+c\pmod n$. Let $n>0$, and suppose $d$ is a balanced lift of $p^{-1}$ with integer phase $c$. If $a$ minimizes $d$ and $d_i-d_a<n$ for every $i$, then
--
--   $$
--   D^a=d,\qquad c_a\equiv c\pmod n.
--   $$
--
--   A lift of width strictly below one period is exactly an anchored lift at any minimum coordinate.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AnchoredPhases.lean#L84-L127

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
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.AnchoredPhases
end LX.AnchoredPhases
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
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.recovers_strict_strip {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p.symm c d) (a : Fin n)
    (hmin : ∀ i, d a ≤ d i) (hwidth : ∀ i, d i-d a < (n : ℤ)) :
    _root_.LX.AnchoredPhases.displacement p a = d ∧ (phase p a : Fin n) = (c : Fin n) := by sorry

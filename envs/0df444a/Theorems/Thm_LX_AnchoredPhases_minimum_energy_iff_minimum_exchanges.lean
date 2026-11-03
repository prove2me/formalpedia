-- Prove2me | Theorems.Thm_LX_AnchoredPhases_minimum_energy_iff_minimum_exchanges
-- name    : LX.AnchoredPhases.minimum_energy_iff_minimum_exchanges
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:58:20.213673+00:00
-- url     : https://prove2.me/theorems/73127b22-004e-4745-b8e8-3ad17202b612
-- title:
--   Energy-minimal and exchange-minimal anchors coincide
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For a permutation $p$ and anchor $a$, let $q_a(i)=p(i)+a-p(a)$, $h_a=|\{i:q_a(i)<i\}|$, $D^a_i=((q_a(i)-i)\bmod n)-h_a$, and $c_a=a-p(a)-h_a$. Assume $n>0$. Set $\mathcal E(d)=\sum_i d_i^2$ and let $I(d)$ be the affine inversion count $\sum_{i<j}|\lfloor((j+d_j)-(i+d_i))/n\rfloor|$. Then
--
--   $$
--   (\forall b,\ \mathcal E(D^a)\le\mathcal E(D^b))\iff(\forall b,\ I(D^a)\le I(D^b)).
--   $$
--
--   This compares the two anchor objectives; total word length also includes rotations.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/AnchorPhasePrice.lean#L67-L85

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
import Definitions.Def_LX_ScanInversions
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
namespace LX.Core.FiniteCoordinates
end LX.Core.FiniteCoordinates
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
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.minimum_energy_iff_minimum_exchanges (p : State n) (a : Fin n) :
    (∀ b,energy (_root_.LX.AnchoredPhases.displacement p a) ≤ energy (_root_.LX.AnchoredPhases.displacement p b)) ↔
      ∀ b,inversions (_root_.LX.AnchoredPhases.displacement p a) ≤ inversions (_root_.LX.AnchoredPhases.displacement p b) := by sorry

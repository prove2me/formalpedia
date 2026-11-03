-- Prove2me | Theorems.Thm_LX_AnchoredPhases_two_fixed_no_offset_one
-- name    : LX.AnchoredPhases.two_fixed_no_offset_one
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:18:55.375606+00:00
-- url     : https://prove2.me/theorems/6437ef21-277e-4384-ae1c-23ab65d01628
-- title:
--   A two-fixed critical majorized board has no offset one
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For a permutation $p$ and anchor $a$, let $q_a(i)=p(i)+a-p(a)$, $h_a=|\{i:q_a(i)<i\}|$, $D^a_i=((q_a(i)-i)\bmod n)-h_a$, and $c_a=a-p(a)-h_a$. Put $u_i=[p(i)-i-(p(a)-a)]_n$, $N_a(t)=|\{i:u_i<t\}|$, $S_a(t)=N_a(t)-t$, and $E_a=\sum_{t=0}^{n-1}\max(S_a(t)-2,0)$. A global minimum anchor minimizes $\sum_i d_i^2$ over all balanced lifts of $p^{-1}$ and all phases. A board is majorized if $2\sum_{i\in S}d_i\le |S|(n-|S|)$ for every subset $S\subseteq I_n$. Assume $D^a$ is majorized, $n=2h_a+2$, and $|\operatorname{Fix}(q_a)|=2$. Then
--
--   $$
--   [p(i)-i-(p(a)-a)]_n\ne1\qquad(i\in I_n).
--   $$
--
--   The first positive offset is incompatible with two negative-extreme fixed coordinates.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/EvenUnitPhaseParity.lean#L16-L49

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
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_MinimumHeightRanks
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
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.PairCore
end LX.PairCore
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.two_fixed_no_offset_one (p : State n) (a : Fin n)
    (hm : Majorized (_root_.LX.AnchoredPhases.displacement p a)) (hn : n=2*height p a+2)
    (hf : (fixedPositions (permutation p a)).card=2) (i : Fin n) :
    (cyclicOffset p a i).val ≠ 1 := by sorry

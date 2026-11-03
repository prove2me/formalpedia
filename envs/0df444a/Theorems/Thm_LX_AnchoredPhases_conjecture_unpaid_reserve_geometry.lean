-- Prove2me | Theorems.Thm_LX_AnchoredPhases_conjecture_unpaid_reserve_geometry
-- name    : LX.AnchoredPhases.conjecture_unpaid_reserve_geometry
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:24:42.948994+00:00
-- url     : https://prove2.me/theorems/6408912a-80f0-462d-97e2-aa5e2732159a
-- title:
--   Reserve geometry of a hypothetical unpaid input
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For a permutation $p$ and anchor $a$, let $q_a(i)=p(i)+a-p(a)$, $h_a=|\{i:q_a(i)<i\}|$, $D^a_i=((q_a(i)-i)\bmod n)-h_a$, and $c_a=a-p(a)-h_a$. Put $u_i=[p(i)-i-(p(a)-a)]_n$, $N_a(t)=|\{i:u_i<t\}|$, $S_a(t)=N_a(t)-t$, and $E_a=\sum_{t=0}^{n-1}\max(S_a(t)-2,0)$. A global minimum anchor minimizes $\sum_i d_i^2$ over all balanced lifts of $p^{-1}$ and all phases. Write $A_a=h_a(n-h_a-1)-I(D^a)$ for the anchor reserve, where $I$ is the affine inversion count. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. Assume $n\ge4$, $m,e\in\mathbb N$, $e\le1$, $n=2m+e$, and that no sorting word has $4|w|<3n^2-8n+4(4-e)$.
--
--   $$
--   \exists a,r,R:\ n>6,\quad a\text{ globally minimal},\quad h_a=m-1=\min_bh_b,\quad1+e\le R,\quad R+2e\le8,\quad S_a(r)=R=\max_tS_a(t),\quad R(R-1-e)\le A_a,\quad e=0\Rightarrow2\le A_a\le n-3,\quad e=1\Rightarrow1\le A_a\le m-1.
--   $$
--
--   The reserve restrictions sharpen the rank description of any input that misses the proposed sorting threshold.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ConjectureObstruction.lean#L12-L91

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
import Definitions.Def_LX_AnchorReserveRigidity
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_MinimumEnergyPhases
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
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.CycleGeometry
end LX.CycleGeometry
namespace LX.EventGeometry
end LX.EventGeometry
namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
namespace LX.FiniteJoin
end LX.FiniteJoin
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.LiftedScan
end LX.LiftedScan
namespace LX.MatchingGeometry
end LX.MatchingGeometry
namespace LX.PairCore
end LX.PairCore
namespace LX.Small4
end LX.Small4
namespace LX.Small5
end LX.Small5
namespace LX.Small6
end LX.Small6
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.conjecture_unpaid_reserve_geometry (hn4 : 4 ≤ n) (p : State n)
    (m e : ℕ) (he : e ≤ 1) (hn : n=2*m+e)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(e : ℤ))) :
    ∃ a r : Fin n,∃ R : ℕ,6 < n ∧ GlobalMinimum p a ∧ height p a+1=m ∧
      (∀ b,height p a ≤ height p b) ∧ 1+e ≤ R ∧ R+2*e ≤ 8 ∧
      rankSurplus p a r.val=R ∧ (∀ t : Fin n,rankSurplus p a t.val ≤ R) ∧
      (R : ℤ)*(R-1-e) ≤ anchorReserve p a ∧
      (e=0 → 2 ≤ anchorReserve p a ∧ anchorReserve p a ≤ (n : ℤ)-3) ∧
      (e=1 → 1 ≤ anchorReserve p a ∧ anchorReserve p a ≤ (m : ℤ)-1) := by sorry

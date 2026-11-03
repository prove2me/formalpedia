-- Prove2me | Theorems.Thm_LX_AnchoredPhases_conjecture_window_terminal_threshold
-- name    : LX.AnchoredPhases.conjecture_window_terminal_threshold
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:17:38.550982+00:00
-- url     : https://prove2.me/theorems/e8d36412-271e-4f50-a99c-404da7fcc6d8
-- title:
--   Classification of terminal window thresholds
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For a permutation $p$ and anchor $a$, let $q_a(i)=p(i)+a-p(a)$, $h_a=|\{i:q_a(i)<i\}|$, $D^a_i=((q_a(i)-i)\bmod n)-h_a$, and $c_a=a-p(a)-h_a$. Put $u_i=[p(i)-i-(p(a)-a)]_n$, $N_a(t)=|\{i:u_i<t\}|$, $S_a(t)=N_a(t)-t$, and $E_a=\sum_{t=0}^{n-1}\max(S_a(t)-2,0)$. A global minimum anchor minimizes $\sum_i d_i^2$ over all balanced lifts of $p^{-1}$ and all phases. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. Let $m,R,g,e\in\mathbb N$, $e\le1$, $n=2m+e>6$, $em+2<n$, $h_a=m-1=\min_bh_b$. Assume every $q_b$ has at most $R+1$ fixed points, $S_a(t)\le R$, and the parity sorting threshold is unpaid as above. Choose $z$ such that, whenever $h_c=m$ and $[c-p(c)]_n\ge R+1$, also $h_z=m$ and $R+1\le[z-p(z)]_n\le[c-p(c)]_n$. If $R+1\le g\le em+2$, put $t=[-g-(p(a)-a)]_n$. Then
--
--   $$
--   S_a(t)\ge2\ \lor\ (-g=p(0)\land h_0=m)\ \lor\ -g=p(z)-z\ \lor\ \exists c:\ p(c)<c,\ h_c=m,\ p(c)-c=-g.
--   $$
--
--   All equalities involving offsets are modulo $n$. The classification identifies the possible occupants of a terminal threshold window.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ConjectureTerminalWindow.lean#L31-L135

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
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_FiniteDescentRank
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
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.PairCore
end LX.PairCore
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.conjecture_window_terminal_threshold (p : State n) (a z : Fin n) (m R g e : ℕ)
    (he : e ≤ 1) (hn : n=2*m+e) (hnlarge : 6 < n) (hupper : e*m+2 < n) (ha : height p a+1=m)
    (hmin : ∀ b,height p a ≤ height p b)
    (hF : ∀ b,(fixedPositions (permutation p b)).card ≤ R+1)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R)
    (hz : ∀ c,height p c=m → R+1 ≤ (c-p c).val →
      height p z=m ∧ R+1 ≤ (z-p z).val ∧ (z-p z).val ≤ (c-p c).val)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(e : ℤ)))
    (hglo : R+1 ≤ g) (hghi : g ≤ e*m+2) :
    2 ≤ rankSurplus p a (-(g : Fin n)-(p a-a)).val ∨
      (-(g : Fin n)=p 0 ∧ height p 0=m) ∨
      -(g : Fin n)=p z-z ∨
      ∃ c : Fin n,c ∈ descendingPositions p ∧ height p c=m ∧ p c-c= -(g : Fin n) := by sorry

-- Prove2me | Theorems.Thm_LX_Antipode_odd_middle_greedy_price_lower
-- name    : LX.Antipode.odd_middle_greedy_price_lower
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:09:56.691838+00:00
-- url     : https://prove2.me/theorems/1cd2c711-4e34-4520-a522-829042af7ced
-- title:
--   Middle phases of every odd antipode lift meet the sharp price
-- statement:
--   Middle phases of every odd antipode lift meet the sharp price.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. $\mathrm{Lift}(p,c,d)$ means $\sum_i d(i)=0$ and $i+d(i)\equiv p^{-1}(i)+c\pmod n$ for every residue $i$. $I(d)=J(i\mapsto\operatorname{rep}(i)+d(i))$ is the affine inversion count of a displacement vector. $\mathrm{Scan}(d,w)$ is a legal greedy scan ending at the zero vector: rotate when $d(0)\le d(1)+1$, exchange otherwise. $P(c,w)=\#_l(w)+\operatorname{rep}(c-\#_l(w))$ counts rotations including the final phase correction. $o_m=(\sigma\rho_m)^{-1}$, where $\sigma(i)=1-i$ and $\rho_m$ sends $2$ to $m+1$, sends $3,\ldots,m+1$ to their predecessors, and fixes other positions. $J(F)=\sum_{i<j}|\lfloor(F(j)-F(i))/n\rfloor|$ is affine inversion count. Words use forward rotation $l:i\mapsto i+1$ and adjacent exchange $x=(0\ 1)$; $\operatorname{ev}(w)$ is their ordered product.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (m : \mathbb N) (hm : 2 \le  m) (hn : n = 2\, m + 1) (c : I_{n}), 2 \le  \operatorname{rep}\,c \to  \operatorname{rep}\,c \le  m + 1 \to  \forall  (d : I_{n} \to  \mathbb Z), \operatorname{Lift} (o m) (\operatorname{rep}\,c) d \to  \forall  (g : \operatorname{Seq} \mathcal A), \operatorname{Scan} d g \to  3\, m ^{2} - m + 1 \le  I d + P c g
--   $$
--
--   This identity can be used while tracking the exact cost or structure of the sorting construction.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/OddMiddleLower.lean#L11-L107

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
import Definitions.Def_LX_GreedyScan
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

theorem LX.Antipode.odd_middle_greedy_price_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {c : Fin n} (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1)
    {d : Fin n → ℤ} (hd : IsLift (odd m hm hn) (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) :
    3*m^2-m+1 ≤ inversions d+paidRotations c g := by sorry

-- Prove2me | Theorems.Thm_LX_AffineScan_reflection_token_bound
-- name    : LX.AffineScan.reflection_token_bound
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:10:24.338579+00:00
-- url     : https://prove2.me/theorems/e1bf2726-8223-43a2-94fe-6d5ea0a222f1
-- title:
--   A reflection-type lift gives a tokenwise lower bound on paid rotations
-- statement:
--   A reflection-type lift gives a tokenwise lower bound on paid rotations.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. $\mathrm{Lift}(p,c,d)$ means $\sum_i d(i)=0$ and $i+d(i)\equiv p^{-1}(i)+c\pmod n$ for every residue $i$. $\mathrm{Scan}(d,w)$ is a legal greedy scan ending at the zero vector: rotate when $d(0)\le d(1)+1$, exchange otherwise. $P(c,w)=\#_l(w)+\operatorname{rep}(c-\#_l(w))$ counts rotations including the final phase correction. Words use forward rotation $l:i\mapsto i+1$ and adjacent exchange $x=(0\ 1)$; $\operatorname{ev}(w)$ is their ordered product.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) , 2 \le  n \to  \forall  (p : \mathfrak S(I_n)) (c : I_{n}) (d : I_{n} \to  \mathbb Z), \operatorname{Lift} p (\operatorname{rep}\,c) d \to  \forall  (g : \operatorname{Seq} \mathcal A), \operatorname{Scan} d g \to  \forall  (\rho : \mathfrak S(I_n)), (\forall  (i : I_{n}), (\operatorname{inverse} p) i = 1 - \rho i) \to  \forall  (i : I_{n}), 1 \le  \operatorname{rep}\,i \to  1 \le  \operatorname{rep}\,(\rho i) \to  \operatorname{rep}\,i + \operatorname{rep}\,(\rho i) - \operatorname{rep}\,n - 1 - (\operatorname{rep}\,n - 1)\, d i \le  \operatorname{rep}\,(P c g)
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/OddMiddlePair.lean#L11-L27

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

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AffineScan.reflection_token_bound (hn : 2 ≤ n) {p : State n} {c : Fin n} {d : Fin n → ℤ}
    (hd : IsLift p (c : ℤ) d) {g : List Letter} (hg : ScanTrace d g)
    (ρ : State n) (hp : ∀ i,p.symm i=1-ρ i) (i : Fin n)
    (hi : 1 ≤ i.val) (hr : 1 ≤ (ρ i).val) :
    (i : ℤ)+(ρ i : ℤ)-(n : ℤ)-1-((n : ℤ)-1)*d i ≤ (paidRotations c g : ℤ) := by sorry

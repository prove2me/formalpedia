-- Prove2me | Theorems.Thm_LX_AffineScan_top_phase_inversions
-- name    : LX.AffineScan.top_phase_inversions
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:58:22.80047+00:00
-- url     : https://prove2.me/theorems/2d05817f-e8a8-4cab-a7e9-57be1729f9e8
-- title:
--   Shifting a top subset of a strict-width lift has an exact inversion-price change
-- statement:
--   Shifting a top subset of a strict-width lift has an exact inversion-price change.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\mathcal P_{\rm fin}(X)$ denotes finite subsets and a subscript $\#$ denotes cardinality. Function symbols are written in curried notation. $\mathrm{Lift}(p,c,d)$ means $\sum_i d(i)=0$ and $i+d(i)\equiv p^{-1}(i)+c\pmod n$ for every residue $i$. $\mathrm{PS}(d,S)(i)=d(i)+|S|-n\mathbf1_{i\in S}$ is the subset phase shift. $I(d)=J(i\mapsto\operatorname{rep}(i)+d(i))$ is the affine inversion count of a displacement vector. $J(F)=\sum_{i<j}|\lfloor(F(j)-F(i))/n\rfloor|$ is affine inversion count.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (c : \mathbb Z) (d : I_{n} \to  \mathbb Z), \operatorname{Lift} p c d \to  \forall  (S : \mathcal P_{\rm fin} (I_{n})), (\forall  (i j : I_{n}), d i - d j < \operatorname{rep}\,n) \to  (\forall  i \in  S, \forall  j \notin  S, d j \le  d i) \to  \operatorname{rep}\,(I (\operatorname{PS} d S)) - \operatorname{rep}\,(I d) = \operatorname{rep}\,S_{\#}\, (\operatorname{rep}\,n - \operatorname{rep}\,S_{\#}) - 2\, \sum_{i\in S} d i
--   $$
--
--   This identity can be used while tracking the exact cost or structure of the sorting construction.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PhaseExchangePrice.lean#L38-L107

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
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace List
end List

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AffineScan.top_phase_inversions {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (S : Finset (Fin n))
    (hwidth : ∀ i j, d i-d j < (n : ℤ))
    (htop : ∀ i ∈ S, ∀ j ∉ S, d j ≤ d i) :
    (inversions (phaseShift d S) : ℤ)-inversions d=
      (S.card : ℤ)*((n : ℤ)-S.card)-2*∑ i ∈ S,d i := by sorry

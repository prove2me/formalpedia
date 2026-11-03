-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_shifted_capacity_equality
-- name    : LX.Core.FiniteCuts.shifted_capacity_equality
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:05:41.486689+00:00
-- url     : https://prove2.me/theorems/02b4269a-f8df-4549-9ef9-d0156eb35832
-- title:
--   Equality in strict-band inversion capacity determines both reflection rank and event length
-- statement:
--   Equality in strict-band inversion capacity determines both reflection rank and event length.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\mathcal P_{\rm fin}(X)$ denotes finite subsets and a subscript $\#$ denotes cardinality. Function symbols are written in curried notation. $\mathrm{Lift}(p,c,d)$ means $\sum_i d(i)=0$ and $i+d(i)\equiv p^{-1}(i)+c\pmod n$ for every residue $i$. $J(F)=\sum_{i<j}|\lfloor(F(j)-F(i))/n\rfloor|$ is affine inversion count. $\operatorname{inv}(p)=|\{(i,j):i<j,\ p(j)<p(i)\}|$ is the ordinary finite inversion number. $\Delta(p,i)=\operatorname{rep}(p(i))-\operatorname{rep}(i)$ is ordinary integer displacement. $\mathrm{Shift}(p,c,h)(i)=p^{-1}(i)+c+h$ modulo $n$. $\operatorname{supp}(p)$ is the moved-point set and $\operatorname{cycles}(p)$ its nontrivial disjoint cycle factors; cycle membership includes fixed singleton orbits.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (c : \mathbb Z) (d : I_{n} \to  \mathbb Z), \operatorname{Lift} p c d \to  \forall  (h : \mathbb Z), (\forall  (i : I_{n}), 0 \le  d i + h \land  d i + h < \operatorname{rep}\,n) \to  \operatorname{rep}\,(J \lambda i \mapsto \operatorname{rep}\,i + d i) = h\, (\operatorname{rep}\,n - h - 1) \to  \text{put }q := \operatorname{Shift} p c h; \operatorname{rep}\,(\operatorname{supp} q)_{\#} - \operatorname{rep}\,(\operatorname{cycles} q)_{\#} = h \land  \sum_{i} |\Delta q i| - \operatorname{rep}\,(\operatorname{inv} q) = h
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/StrictBandEquality.lean#L8-L33

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
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteWindowInversions
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
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.Core.FiniteCuts.shifted_capacity_equality {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (h : ℤ)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ))
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      h*((n : ℤ)-h-1)) :
    let q := shiftedLiftPermutation p c h
    (q.support.card : ℤ)-(q.cycleFactorsFinset.card : ℤ)=h ∧
      (∑ i, |_root_.LX.Core.FiniteCuts.displacement q i|)-(inversionNumber q : ℤ)=h := by sorry

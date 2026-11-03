-- Prove2me | Theorems.Thm_LX_AnchoredPhases_zero_slack_phase
-- name    : LX.AnchoredPhases.zero_slack_phase
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:11:45.135364+00:00
-- url     : https://prove2.me/theorems/5637e105-802a-40f0-ba97-79676a42aeb3
-- title:
--   A tight majorization subset shifts a global minimum to another global minimum without changing inversions
-- statement:
--   A tight majorization subset shifts a global minimum to another global minimum without changing inversions.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\mathcal P_{\rm fin}(X)$ denotes finite subsets and a subscript $\#$ denotes cardinality. Function symbols are written in curried notation. $d_A(p,a)(i)=\operatorname{rep}(p(i)-i-(p(a)-a))-h(p,a)$ is the balanced anchored displacement. $\phi(p,a)=\operatorname{rep}(a)-\operatorname{rep}(p(a))-h(p,a)$ is its integer phase. $\mathrm{GM}(p,a)$ means that this anchor minimizes $\sum_i d(i)^2$ over all balanced lifts of $p^{-1}$ and all phases. $\mathrm{PS}(d,S)(i)=d(i)+|S|-n\mathbf1_{i\in S}$ is the subset phase shift. $I(d)=J(i\mapsto\operatorname{rep}(i)+d(i))$ is the affine inversion count of a displacement vector. $h(p,a)=|\{i:q(p,a)(i)<i\}|$ counts its ordinary descending arrows. $J(F)=\sum_{i<j}|\lfloor(F(j)-F(i))/n\rfloor|$ is affine inversion count. $q(p,a)(i)=p(i)+a-p(a)$ is the anchored permutation, with arithmetic in the residue circle.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (a : I_{n}), \operatorname{GM} p a \to  \forall  (S : \mathcal P_{\rm fin} (I_{n})), 2\, \sum_{i\in S} d_A p a i = \operatorname{rep}\,S_{\#}\, (\operatorname{rep}\,n - \operatorname{rep}\,S_{\#}) \to  \exists  b, \operatorname{GM} p b \land  d_A p b = \operatorname{PS} (d_A p a) S \land  \operatorname{rep}\,(\phi p b) = \operatorname{rep}\,(\phi p a) + \operatorname{rep}\,S_{\#} \land  I (d_A p b) = I (d_A p a)
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/MinimumEnergyPhases.lean#L43-L68

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
import Definitions.Def_LX_MinimumEnergyPhases
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

theorem LX.AnchoredPhases.zero_slack_phase {p : State n} {a : Fin n} (ha : GlobalMinimum p a)
    (S : Finset (Fin n))
    (htight : 2*(∑ i ∈ S,_root_.LX.AnchoredPhases.displacement p a i)=(S.card : ℤ)*((n : ℤ)-S.card)) :
    ∃ b : Fin n, GlobalMinimum p b ∧
      _root_.LX.AnchoredPhases.displacement p b=phaseShift (_root_.LX.AnchoredPhases.displacement p a) S ∧
      (phase p b : Fin n)=(phase p a : Fin n)+(S.card : Fin n) ∧
      inversions (_root_.LX.AnchoredPhases.displacement p b)=inversions (_root_.LX.AnchoredPhases.displacement p a) := by sorry

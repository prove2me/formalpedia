-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_exists_descent
-- name    : LX.Core.ZeroGap.exists_descent
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:59:20.854813+00:00
-- url     : https://prove2.me/theorems/7326df37-8b48-4c1f-bae2-7873edaa0321
-- title:
--   Every nonzero short zero-phase lift admits a zero-gap descent with exact mass and inversion drops
-- statement:
--   Every nonzero short zero-phase lift admits a zero-gap descent with exact mass and inversion drops.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{Lift}(p,c,d)$ means $\sum_i d(i)=0$ and $i+d(i)\equiv p^{-1}(i)+c\pmod n$ for every residue $i$. $J(F)=\sum_{i<j}|\lfloor(F(j)-F(i))/n\rfloor|$ is affine inversion count. $X_{\rm gap}(d,v)$ replaces $d(0)$ by $\operatorname{rep}(v)+d(v)$ and $d(v)$ by $d(0)-\operatorname{rep}(v)$, leaving other entries unchanged. $\mathrm{Loc}(d,r)(i)=d(i+r)$ is the displacement seen from the recentered origin. $\mathrm{Target}(p,c,r)^{-1}(i)=p^{-1}(i+r)+c-r$ defines the recentered target.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (d : I_{n} \to  \mathbb Z), \operatorname{Lift} p 0 d \to  (\forall  (i : I_{n}), 2\, |d i| < \operatorname{rep}\,n) \to  (\exists  i, d i \ne  0) \to  \exists  u v, 0 < \operatorname{rep}\,v \land  0 < \operatorname{Loc} d u 0 \land  \operatorname{Loc} d u v < 0 \land  (\forall  (i : I_{n}), 0 < \operatorname{rep}\,i \to  \operatorname{rep}\,i < \operatorname{rep}\,v \to  \operatorname{Loc} d u i = 0) \land  \operatorname{Lift} (\operatorname{swap} 0 v\, \operatorname{Target} p 0 u) 0 (X_{\rm gap} (\operatorname{Loc} d u) v) \land  (\forall  (i : I_{n}), 2\, |X_{\rm gap} (\operatorname{Loc} d u) v i| < \operatorname{rep}\,n) \land  \sum_{i} |d i| = \sum_{i} |X_{\rm gap} (\operatorname{Loc} d u) v i| + 2\, \operatorname{rep}\,v \land  (J \lambda i \mapsto \operatorname{rep}\,i + d i) = (J \lambda i \mapsto \operatorname{rep}\,i + X_{\rm gap} (\operatorname{Loc} d u) v i) + (2\, \operatorname{rep}\,v - 1)
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapDescent.lean#L46-L72

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ZeroGapExchange

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

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.Core.ZeroGap.exists_descent {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) (hne : ∃ i, d i ≠ 0) :
    ∃ u v : Fin n,
      0 < v.val ∧ 0 < RotationWords.localDisplacement d u 0 ∧ RotationWords.localDisplacement d u v < 0 ∧
      (∀ i : Fin n, 0 < i.val → i.val < v.val → RotationWords.localDisplacement d u i=0) ∧
      AffineLift.IsLift (Equiv.swap 0 v*RotationWords.localTarget p 0 u) 0
        (exchange (RotationWords.localDisplacement d u) v) ∧
      (∀ i, 2*|exchange (RotationWords.localDisplacement d u) v i| < (n : ℤ)) ∧
      (∑ i : Fin n, |d i|)=(∑ i : Fin n, |exchange (RotationWords.localDisplacement d u) v i|)+2*(v : ℤ) ∧
      LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i)=
        LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+exchange (RotationWords.localDisplacement d u) v i)+
          (2*v.val-1) := by sorry

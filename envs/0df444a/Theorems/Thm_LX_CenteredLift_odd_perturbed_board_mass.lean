-- Prove2me | Theorems.Thm_LX_CenteredLift_odd_perturbed_board_mass
-- name    : LX.CenteredLift.odd_perturbed_board_mass
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:09:55.643954+00:00
-- url     : https://prove2.me/theorems/572b60ea-07fb-4d10-8b13-2a378b25002b
-- title:
--   A rank perturbation moving each rank back by at most one loses at most one period of centered mass
-- statement:
--   A rank perturbation moving each rank back by at most one loses at most one period of centered mass.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{Pert}(m,C,\rho)(i)$ is the representative of $C-\rho(i)-i$ in $[-m,n-m)$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (m : \mathbb N), n = 2\, m + 1 \to  \forall  (C : \mathbb Z) (\rho : \mathfrak S(I_n)), (\forall  (i : I_{n}), \operatorname{rep}\,i - \operatorname{rep}\,(\rho i) \le  1) \to  -\operatorname{rep}\,n \le  \sum_{i} \operatorname{Pert} m C \rho i
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/OddCenteredMass.lean#L64-L95

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
import Definitions.Def_LX_OddCenteredMass
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.CenteredLift
end LX.CenteredLift
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace List
end List

namespace LX.CenteredLift
end LX.CenteredLift
open LX
open LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.CenteredLift.odd_perturbed_board_mass (m : ℕ) (hn : n=2*m+1) (C : ℤ) (ρ : State n)
    (hr : ∀ i : Fin n,(i : ℤ)-(ρ i : ℤ) ≤ 1) :
    -(n : ℤ) ≤ ∑ i : Fin n,perturbedBoard m C ρ i := by sorry

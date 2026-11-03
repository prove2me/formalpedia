-- Prove2me | Theorems.Thm_LX_AffineScan_reflection_perturbation_pairs
-- name    : LX.AffineScan.reflection_perturbation_pairs
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:00:27.328288+00:00
-- url     : https://prove2.me/theorems/0ec8dc61-7889-4f21-a7de-bf343536fb36
-- title:
--   Same-parity winding pairs are charged to affine inversions or finite rank inversions
-- statement:
--   Same-parity winding pairs are charged to affine inversions or finite rank inversions.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $I(d)=J(i\mapsto\operatorname{rep}(i)+d(i))$ is the affine inversion count of a displacement vector. $F(d)(i)=\operatorname{rep}(i)+d(i)$ is the lifted target. $\operatorname{inv}(p)=|\{(i,j):i<j,\ p(j)<p(i)\}|$ is the ordinary finite inversion number. $\operatorname{mono}(\chi)$ counts pairs $i<j$ of equal Boolean color. $J(F)=\sum_{i<j}|\lfloor(F(j)-F(i))/n\rfloor|$ is affine inversion count.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (d : I_{n} \to  \mathbb Z) (\rho : \mathfrak S(I_n)) (C : \mathbb Z) (k : I_{n} \to  \mathbb Z), (\forall  (i : I_{n}), F d i = C - \operatorname{rep}\,(\rho i) + \operatorname{rep}\,n\, k i) \to  (\operatorname{mono} \lambda i \mapsto \operatorname{bool} (k i\bmod 2 = 0)) \le  I d + \operatorname{inv} \rho
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ReflectionLiftLower.lean#L10-L49

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
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_TwoColorPairs
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
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
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

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.AffineScan.reflection_perturbation_pairs (d : Fin n → ℤ) (ρ : State n)
    (C : ℤ) (k : Fin n → ℤ)
    (hF : ∀ i,targets d i=C-(ρ i : ℤ)+(n : ℤ)*k i) :
    sameColorPairs (fun i => decide (k i % 2=0)) ≤
      inversions d+LX.Core.FiniteCuts.inversionNumber ρ := by sorry

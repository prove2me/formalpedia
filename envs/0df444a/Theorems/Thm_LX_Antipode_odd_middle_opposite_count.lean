-- Prove2me | Theorems.Thm_LX_Antipode_odd_middle_opposite_count
-- name    : LX.Antipode.odd_middle_opposite_count
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:10:16.414398+00:00
-- url     : https://prove2.me/theorems/d4e394ed-bb46-4d98-a1d7-d818099883f5
-- title:
--   There are enough opposite-parity middle winding coordinates to supply the extra odd lower cost
-- statement:
--   There are enough opposite-parity middle winding coordinates to supply the extra odd lower cost.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $o_m=(\sigma\rho_m)^{-1}$, where $\sigma(i)=1-i$ and $\rho_m$ sends $2$ to $m+1$, sends $3,\ldots,m+1$ to their predecessors, and fixes other positions. $\mathrm{Base}(m,c)$ is the centered representative of $c+1-\rho_m(i)-i$ at coordinate $i$, with $\rho_m(2)=m+1$, $\rho_m(i)=i-1$ for $3\le i\le m+1$, and $\rho_m(i)=i$ elsewhere. $\mathrm{Wind}(m,c,i)$ is the integer winding quotient in the centered decomposition of $c+1-\rho_m(i)-i$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (m : \mathbb N) (hm : 2 \le  m) (hn : n = 2\, m + 1) (c : I_{n}), 2 \le  \operatorname{rep}\,c \to  \operatorname{rep}\,c \le  m + 1 \to  (m - \operatorname{rep}\,c + 1) / 2 \le  \{j\mid 2 < \operatorname{rep}\,j \land  \operatorname{rep}\,j \le  m + 1 \land  \operatorname{bool} (\operatorname{Wind} m c 2\bmod 2 = 0) \ne  \operatorname{bool} (\operatorname{Wind} m c j\bmod 2 = 0)\}_{\#}
--   $$
--
--   This identity can be used while tracking the exact cost or structure of the sorting construction.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/OddMiddleInversions.lean#L62-L87

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
import Definitions.Def_LX_OddMiddleInversions

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
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
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace LX.LiftedScan
end LX.LiftedScan
namespace List
end List

namespace LX.Antipode
end LX.Antipode
open LX
open LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]

theorem LX.Antipode.odd_middle_opposite_count (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1) :
    (m-c.val+1)/2 ≤ (Finset.univ.filter fun j : Fin n =>
      2 < j.val ∧ j.val ≤ m+1 ∧
      decide (oddBaseWinding m hm hn c 2 % 2=0) ≠
        decide (oddBaseWinding m hm hn c j % 2=0)).card := by sorry

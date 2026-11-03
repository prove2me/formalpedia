-- Prove2me | Theorems.Thm_LX_Antipode_odd_special_wrap_mass
-- name    : LX.Antipode.odd_special_wrap_mass
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:10:33.125072+00:00
-- url     : https://prove2.me/theorems/0ea2facb-2fe0-4cd0-9265-3a88ec132fa1
-- title:
--   A sufficiently negative distinguished reflection coordinate contributes a positive period to odd-base mass
-- statement:
--   A sufficiently negative distinguished reflection coordinate contributes a positive period to odd-base mass.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{Ref}(m,C)(i)$ is the unique representative of $C-2i$ in $[-m,n-m)$. $o_m=(\sigma\rho_m)^{-1}$, where $\sigma(i)=1-i$ and $\rho_m$ sends $2$ to $m+1$, sends $3,\ldots,m+1$ to their predecessors, and fixes other positions. $\mathrm{Base}(m,c)$ is the centered representative of $c+1-\rho_m(i)-i$ at coordinate $i$, with $\rho_m(2)=m+1$, $\rho_m(i)=i-1$ for $3\le i\le m+1$, and $\rho_m(i)=i$ elsewhere. $\mathrm{Top}(m,c)=\{i:3\le i\le m+1,\ \mathrm{Ref}(m,c+1)(i)=m\}$.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (m : \mathbb N) (hm : 2 \le  m) (hn : n = 2\, m + 1) (c : I_{n}), \operatorname{Ref} m (\operatorname{rep}\,c + 1) 2 \le  -2 \to  \operatorname{rep}\,n - \operatorname{rep}\,n\, \operatorname{rep}\,(\operatorname{Top} m c)_{\#} \le  \sum_{i} \operatorname{Base} m c i
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/OddOuterMass.lean#L33-L100

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
import Definitions.Def_LX_OddOuterMass
import Definitions.Def_LX_OddSingleRaise

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

theorem LX.Antipode.odd_special_wrap_mass (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hw : reflectionBoard m ((c : ℤ)+1) (2 : Fin n) ≤ -2) :
    (n : ℤ)-(n : ℤ)*(oddMidTop m c).card ≤ ∑ i,oddBase m hm hn c i := by sorry

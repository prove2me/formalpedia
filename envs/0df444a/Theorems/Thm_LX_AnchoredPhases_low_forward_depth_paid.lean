-- Prove2me | Theorems.Thm_LX_AnchoredPhases_low_forward_depth_paid
-- name    : LX.AnchoredPhases.low_forward_depth_paid
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:17:33.755712+00:00
-- url     : https://prove2.me/theorems/9a76285a-71ee-4a5e-9079-61aeb56cc772
-- title:
--   A forward last representative with sufficient depth budget admits a word paying the quadratic term
-- statement:
--   A forward last representative with sufficient depth budget admits a word paying the quadratic term.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. An existential $w$ is a finite word in these generators. Natural subtraction is truncated at zero; scalar price expressions and quantities coerced by $\operatorname{rep}$ are read in the integers. The identity permutation is $1$. $h(p,a)=|\{i:q(p,a)(i)<i\}|$ counts its ordinary descending arrows. $d_A(p,a)(i)=\operatorname{rep}(p(i)-i-(p(a)-a))-h(p,a)$ is the balanced anchored displacement. $N(d,k)=|\{i:\beta(d,i)\ge k\}|$ counts tokens at or above depth $k$. Words use forward rotation $l:i\mapsto i+1$ and adjacent exchange $x=(0\ 1)$; $\operatorname{ev}(w)$ is their ordered product. $q(p,a)(i)=p(i)+a-p(a)$ is the anchored permutation, with arithmetic in the residue circle. $\beta(d,i)=\sum_j\max(-C(d,i,j),0)$ is backward depth. $C(d,i,j)=-\lfloor(\operatorname{rep}(j-i)+d(j)-d(i))/n\rfloor$ is signed affine crossing multiplicity.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (b : I_{n}), 2 \le  h p b \to  n = 2\, h p b + 2 \lor  n = 2\, h p b + 3 \to  p 0 \ne  p b - b \to  (\forall  (i : I_{n}), p i - i = p b - b \to  \operatorname{rep}\,i \le  \operatorname{rep}\,b) \to  \neg \operatorname{rep}\,(p b) < \operatorname{rep}\,b \to  0 < \operatorname{rep}\,(b - p b) \to  N (d_A p b) (h p b - 1) \le  \operatorname{rep}\,(b - p b) \to  \exists  w, p\, \operatorname{ev} w = 1 \land  4\, \operatorname{rep}\,w_{\ell} \le  3\, \operatorname{rep}\,n ^{2} - 8\, \operatorname{rep}\,n
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/LowForwardPayment.lean#L11-L39

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
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_DepthCrowding
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
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.PairCore
end LX.PairCore
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.low_forward_depth_paid (p : State n) (b : Fin n)
    (hh : 2 ≤ height p b) (hn : n=2*height p b+2 ∨ n=2*height p b+3)
    (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hback : ¬(p b).val < b.val) (hgap : 0 < (b-p b).val)
    (hdepth : depthCount (_root_.LX.AnchoredPhases.displacement p b) (height p b-1) ≤ (b-p b).val) :
    ∃ w : List Letter,p*eval w=1 ∧ 4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n := by sorry

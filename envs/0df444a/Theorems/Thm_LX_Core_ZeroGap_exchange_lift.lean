-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_exchange_lift
-- name    : LX.Core.ZeroGap.exchange_lift
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:58:49.967642+00:00
-- url     : https://prove2.me/theorems/8939ec16-d581-4db7-b0f0-563829ec3689
-- title:
--   The endpoint exchange updates the target permutation by the matching transposition and remains a balanced zero-phase lift
-- statement:
--   The endpoint exchange updates the target permutation by the matching transposition and remains a balanced zero-phase lift.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $\mathrm{Lift}(p,c,d)$ means $\sum_i d(i)=0$ and $i+d(i)\equiv p^{-1}(i)+c\pmod n$ for every residue $i$. $X_{\rm gap}(d,v)$ replaces $d(0)$ by $\operatorname{rep}(v)+d(v)$ and $d(v)$ by $d(0)-\operatorname{rep}(v)$, leaving other entries unchanged.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (d : I_{n} \to  \mathbb Z), \operatorname{Lift} p 0 d \to  \forall  (v : I_{n}), v \ne  0 \to  \operatorname{Lift} (\operatorname{swap} 0 v\, p) 0 (X_{\rm gap} d v)
--   $$
--
--   This identity can be used while tracking the exact cost or structure of the sorting construction.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapExchange.lean#L64-L83

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
import Definitions.Def_LX_ZeroGapExchange

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
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

theorem LX.Core.ZeroGap.exchange_lift {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (v : Fin n) (hv : v ≠ 0) :
    AffineLift.IsLift (Equiv.swap 0 v*p) 0 (exchange d v) := by sorry

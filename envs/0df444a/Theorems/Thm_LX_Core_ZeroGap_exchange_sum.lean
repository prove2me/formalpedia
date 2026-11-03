-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_exchange_sum
-- name    : LX.Core.ZeroGap.exchange_sum
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:58:50.027203+00:00
-- url     : https://prove2.me/theorems/13b71f9c-1edd-496e-bc33-78b2fee7f985
-- title:
--   Summing any integer function after endpoint exchange changes only the two endpoint terms
-- statement:
--   Summing any integer function after endpoint exchange changes only the two endpoint terms.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. $X_{\rm gap}(d,v)$ replaces $d(0)$ by $\operatorname{rep}(v)+d(v)$ and $d(v)$ by $d(0)-\operatorname{rep}(v)$, leaving other entries unchanged.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (d : I_{n} \to  \mathbb Z) (v : I_{n}), v \ne  0 \to  \forall  (f : \mathbb Z \to  \mathbb Z), \sum_{i} f (X_{\rm gap} d v i) = \sum_{i} f (d i) + (f (\operatorname{rep}\,v + d v) - f (d 0)) + (f (d 0 - \operatorname{rep}\,v) - f (d v))
--   $$
--
--   This identity can be used while tracking the exact cost or structure of the sorting construction.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ZeroGapExchange.lean#L13-L27

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

theorem LX.Core.ZeroGap.exchange_sum (d : Fin n → ℤ) (v : Fin n) (hv : v ≠ 0) (f : ℤ → ℤ) :
    (∑ i : Fin n, f (exchange d v i))=(∑ i : Fin n, f (d i))+
      (f ((v : ℤ)+d v)-f (d 0))+(f (d 0-(v : ℤ))-f (d v)) := by sorry
